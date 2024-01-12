#include "sr_plan.h"
#include "commands/defrem.h"
#include "commands/event_trigger.h"
#include "commands/extension.h"
#include "catalog/pg_extension.h"
#include "catalog/indexing.h"
#include "access/sysattr.h"
#include "access/xact.h"
#include "access/hash.h"
#include "utils/lsyscache.h"
#include "utils/memutils.h"
#include "miscadmin.h"
#include "cJSON.h"
#include "postgres.h"
#include "outfuncs_sr.h"
#if PG_VERSION_NUM >= 100000
#include "utils/queryenvironment.h"
#include "catalog/index.h"
#include "regex.h"
#include "nodes/parsenodes.h"
#endif
#include "catalog/pg_operator.h"
#include "utils/syscache.h"

#if PG_VERSION_NUM >= 120000
#include "catalog/pg_extension_d.h"
#endif

PG_MODULE_MAGIC;

PG_FUNCTION_INFO_V1(do_nothing);
PG_FUNCTION_INFO_V1(show_plan);
PG_FUNCTION_INFO_V1(_p);

void _PG_init(void);
void _PG_fini(void);

static planner_hook_type srplan_planner_hook_next = NULL;
post_parse_analyze_hook_type srplan_post_parse_analyze_hook_next = NULL;
static char *ML_host = NULL;
static int ML_port = 9381;
static bool ML_enabled = false;
static int sr_count = 2;

typedef struct StrPair
{
    char *key;
    char *value;
} StrPair;

typedef struct StrHashMap
{
    StrPair *pairs;
    int size;
    int capacity;
} StrHashMap;

typedef struct SrPlanCachedInfo
{
    bool enabled;
    bool write_mode;
    bool explain_query;
    int log_usage;
    Oid fake_func;
    Oid schema_oid;
    Oid sr_plans_oid;
    Oid sr_index_oid;
    Oid reloids_index_oid;
    Oid index_reloids_index_oid;
    const char *query_text;
} SrPlanCachedInfo;
typedef struct JoinCond
{
    char t1[50];
    char c1[50];
    char t2[50];
    char c2[50];
} JoinCond;
typedef struct show_plan_funcctx
{
    ExplainFormat format;
    char *output;
    int lines_count;
} show_plan_funcctx;

SrPlanCachedInfo cachedInfo = {
    true,       /* enabled */
    false,      /* write_mode */
    false,      /* explain_query */
    0,          /* log_usage */
    0,          /* fake_func */
    InvalidOid, /* schema_oid */
    InvalidOid, /* sr_plans_reloid */
    InvalidOid, /* sr_plans_index_oid */
    InvalidOid, /* reloids_index_oid */
    InvalidOid, /* index_reloids_index_oid */
    NULL};

#if PG_VERSION_NUM >= 130000
static PlannedStmt *sr_planner(Query *parse, const char *query_string,
                               int cursorOptions, ParamListInfo boundParams);
#else
static PlannedStmt *sr_planner(Query *parse, int cursorOptions,
                               ParamListInfo boundParams);
#endif
List *lookup_plan_by_query_hash_list(MemoryContext tmpctx, Snapshot snapshot, Relation sr_index_rel,
                                     Relation sr_plans_heap, ScanKey key,
                                     void *context,
                                     int index,
                                     char **queryString, int *count);
JoinCond *GetJoinConds(const char *sql, int *num, MemoryContext _tm);
static void sr_analyze(ParseState *pstate, Query *query);
static Oid get_sr_plan_schema(void);
static Oid sr_get_relname_oid(Oid schema_oid, const char *relname);
static bool sr_query_walker(Query *node, void *context);
static bool sr_query_expr_walker(Node *node, void *context);
void walker_callback(void *node);
static void sr_plan_relcache_hook(Datum arg, Oid relid);
static Oid getOptName(Oid opno);
char *get_json_plan(PlannedStmt *pl_stmt);

static void plan_tree_visitor(Plan *plan,
                              void (*visitor)(Plan *plan, void *context),
                              void *context);
static void execute_for_plantree(PlannedStmt *planned_stmt,
                                 void (*proc)(void *context, Plan *plan),
                                 void *context);
static void restore_params(void *context, Plan *plan);
static Datum get_query_hash(Query *node);
static int connect_to_ML(const char *host, int port);
static void collect_indexid(void *context, Plan *plan);
static bool
sr_query_fake_const_walker(Node *node, void *context);
StrHashMap *create_str_hash_map(void);
void str_hash_map_insert(StrHashMap *map, const char *key, const char *value);
const char *str_hash_map_lookup(StrHashMap *map, const char *key);
char *get_json_plan_cost(PlannedStmt *pl_stmt);
void bulidAliasMap(cJSON *json, StrHashMap *map);
void processJson(cJSON *json, StrHashMap *map);
struct QueryParam
{
    int location;
    int funccollid;
    void *node;
    int order;
};

struct QueryParamsContext
{
    bool collect;
    int travel_o;
    int travel_p;
    List *params;
    List *optparams;
};
struct OpParam
{
    Oid opno;
    Oid opfuncid;
    int location;
    int order;
};

struct IndexIds
{
    List *ids;
};

List *query_params;

static void
invalidate_oids(void)
{
    cachedInfo.schema_oid = InvalidOid;
    cachedInfo.sr_plans_oid = InvalidOid;
    cachedInfo.sr_index_oid = InvalidOid;
    cachedInfo.fake_func = InvalidOid;
    cachedInfo.reloids_index_oid = InvalidOid;
    cachedInfo.index_reloids_index_oid = InvalidOid;
}
static Oid getOptName(Oid opno)
{
    HeapTuple opertup;
    Oid fake_oid;
    Datum opt_hash;
    char *oprname = NULL;
    fake_oid = 0;
    opertup = SearchSysCache1(OPEROID, ObjectIdGetDatum(opno));
    if (HeapTupleIsValid(opertup))
    {
        Form_pg_operator operform = (Form_pg_operator)GETSTRUCT(opertup);
        char *oprname = NameStr(operform->oprname);
        opt_hash = hash_any((unsigned char *)oprname, strlen(oprname));
        ReleaseSysCache(opertup);
        if (opt_hash > UINT32_MAX)
        {
            // Datum is too large, reduce it to fit into an Oid.
            // Here we simply take the modulo, but you might want to use a different strategy.
            fake_oid = (Oid)(opt_hash % UINT32_MAX + 1);
        }
        else
        {
            // Datum fits into an Oid, just cast it.
            fake_oid = (Oid)opt_hash;
        }

        return fake_oid;
    }
    return fake_oid;
}

static bool
init_sr_plan(void)
{
    char *schema_name;
    List *func_name_list;

    Oid args[1] = {ANYELEMENTOID};
    static bool relcache_callback_needed = true;

    cachedInfo.schema_oid = get_sr_plan_schema();
    if (cachedInfo.schema_oid == InvalidOid)
        return false;

    cachedInfo.sr_index_oid = sr_get_relname_oid(cachedInfo.schema_oid,
                                                 SR_PLANS_TABLE_QUERY_INDEX_NAME);
    cachedInfo.sr_plans_oid = sr_get_relname_oid(cachedInfo.schema_oid,
                                                 SR_PLANS_TABLE_NAME);
    cachedInfo.reloids_index_oid = sr_get_relname_oid(cachedInfo.schema_oid,
                                                      SR_PLANS_RELOIDS_INDEX);
    cachedInfo.index_reloids_index_oid = sr_get_relname_oid(cachedInfo.schema_oid,
                                                            SR_PLANS_INDEX_RELOIDS_INDEX);

    if (cachedInfo.sr_plans_oid == InvalidOid ||
        cachedInfo.sr_index_oid == InvalidOid)
    {
        elog(WARNING, "sr_plan extension installed incorrectly. Do nothing. It's ok in pg_restore.");
        return false;
    }
    /* Initialize _p function Oid */
    schema_name = get_namespace_name(cachedInfo.schema_oid);
    func_name_list = list_make2(makeString(schema_name), makeString("_p"));
    cachedInfo.fake_func = LookupFuncName(func_name_list, 1, args, true);
    list_free(func_name_list);
    pfree(schema_name);

    if (cachedInfo.fake_func == InvalidOid)
    {
        elog(WARNING, "sr_plan extension installed incorrectly");
        return false;
    }
    if (relcache_callback_needed)
    {
        CacheRegisterRelcacheCallback(sr_plan_relcache_hook, PointerGetDatum(NULL));
        relcache_callback_needed = false;
    }
    return true;
}

/*
 * Check if 'stmt' is ALTER EXTENSION sr_plan
 */
static bool
is_alter_extension_cmd(Node *stmt)
{
    if (!stmt)
        return false;

    if (!IsA(stmt, AlterExtensionStmt))
        return false;

    if (pg_strcasecmp(((AlterExtensionStmt *)stmt)->extname, "sr_plan") == 0)
        return true;

    return false;
}

static bool
is_drop_extension_stmt(Node *stmt)
{
    char *objname;
    DropStmt *ds = (DropStmt *)stmt;

    if (!stmt)
        return false;

    if (!IsA(stmt, DropStmt))
        return false;

#if PG_VERSION_NUM < 100000
    objname = strVal(linitial(linitial(ds->objects)));
#else
    objname = strVal(linitial(ds->objects));
#endif

    if (ds->removeType == OBJECT_EXTENSION &&
        pg_strcasecmp(objname, "sr_plan") == 0)
        return true;

    return false;
}
static int connect_to_ML(const char *host, int port)
{
    int ret, conn_fd;
    struct sockaddr_in server_addr = {0};

    server_addr.sin_family = AF_INET;
    server_addr.sin_port = htons(port);
    inet_pton(AF_INET, host, &server_addr.sin_addr);
    conn_fd = socket(AF_INET, SOCK_STREAM, 0);
    if (conn_fd < 0)
    {
        return conn_fd;
    }

    ret = connect(conn_fd, (struct sockaddr *)&server_addr, sizeof(server_addr));
    if (ret == -1)
    {
        return ret;
    }

    return conn_fd;
}

static void write_all_to_socket(int conn_fd, const char *json)
{
    size_t json_length;
    ssize_t written, written_total;
    json_length = strlen(json);
    written_total = 0;

    while (written_total != json_length)
    {
        written = write(conn_fd,
                        json + written_total,
                        json_length - written_total);
        written_total += written;
    }
}

static void
sr_plan_relcache_hook(Datum arg, Oid relid)
{
    if (relid == InvalidOid || (relid == cachedInfo.sr_plans_oid))
        invalidate_oids();
}

/*
 * TODO: maybe support for EXPLAIN (cached 1)
static void
check_for_explain_cached(ExplainStmt *stmt)
{
    List		*reslist;
    ListCell	*lc;

    if (!IsA(stmt, ExplainStmt))
        return;

    reslist = NIL;

    foreach(lc, stmt->options)
    {
        DefElem    *opt = (DefElem *) lfirst(lc);

        if (strcmp(opt->defname, "cached") == 0 &&
                strcmp(defGetString(opt), "on") == 0)
            cachedInfo.explain_query = true;
        else
            reslist = lappend(reslist, opt);
    }

    stmt->options = reslist;
}*/

static void
sr_analyze(ParseState *pstate, Query *query)
{
    cachedInfo.query_text = pstate->p_sourcetext;
    cachedInfo.explain_query = false;

    if (query->commandType == CMD_UTILITY)
    {
        if (IsA(query->utilityStmt, ExplainStmt))
            cachedInfo.explain_query = true;

        /* ... ALTER EXTENSION sr_plan */
        if (is_alter_extension_cmd(query->utilityStmt))
            invalidate_oids();

        /* ... DROP EXTENSION sr_plan */
        if (is_drop_extension_stmt(query->utilityStmt))
        {
            invalidate_oids();
            cachedInfo.enabled = false;
            elog(NOTICE, "sr_plan was disabled");
        }
    }

    if (srplan_post_parse_analyze_hook_next)
        srplan_post_parse_analyze_hook_next(pstate, query);
}

/*
 * Return sr_plan schema's Oid or InvalidOid if that's not possible.
 */
static Oid
get_sr_plan_schema(void)
{
    Oid result;
    Relation rel;
    SysScanDesc scandesc;
    HeapTuple tuple;
    ScanKeyData entry[1];
    Oid ext_schema;
    LOCKMODE heap_lock = AccessShareLock;

    /* It's impossible to fetch sr_plan's schema now */
    if (!IsTransactionState())
        return InvalidOid;

    ext_schema = get_extension_oid("sr_plan", true);
    if (ext_schema == InvalidOid)
        return InvalidOid; /* exit if sr_plan does not exist */

#if PG_VERSION_NUM >= 120000
    ScanKeyInit(&entry[0],
                Anum_pg_extension_oid,
                BTEqualStrategyNumber, F_OIDEQ,
                ObjectIdGetDatum(ext_schema));
#else
    ScanKeyInit(&entry[0],
                ObjectIdAttributeNumber,
                BTEqualStrategyNumber, F_OIDEQ,
                ObjectIdGetDatum(ext_schema));
#endif

#if PG_VERSION_NUM >= 130000
    rel = table_open(ExtensionRelationId, heap_lock);
#else
    rel = heap_open(ExtensionRelationId, heap_lock);
#endif
    scandesc = systable_beginscan(rel, ExtensionOidIndexId, true,
                                  NULL, 1, entry);

    tuple = systable_getnext(scandesc);

    /* We assume that there can be at most one matching tuple */
    if (HeapTupleIsValid(tuple))
        result = ((Form_pg_extension)GETSTRUCT(tuple))->extnamespace;
    else
        result = InvalidOid;

    systable_endscan(scandesc);

#if PG_VERSION_NUM >= 130000
    table_close(rel, heap_lock);
#else
    heap_close(rel, heap_lock);
#endif

    return result;
}

/*
 * Return Oid of relation in sr_plan extension schema or
 * InvalidOid if that's not possible.
 */

static Oid
sr_get_relname_oid(Oid schema_oid, const char *relname)
{
    if (schema_oid == InvalidOid)
        schema_oid = get_sr_plan_schema();

    if (schema_oid == InvalidOid)
        return InvalidOid;

    return get_relname_relid(relname, schema_oid);
}

static void
params_restore_visitor(Plan *plan, void *context)
{
    expression_tree_walker((Node *)plan->qual, sr_query_expr_walker, context);
    expression_tree_walker((Node *)plan->targetlist, sr_query_expr_walker, context);
}

static void
restore_params(void *context, Plan *plan)
{

    plan_tree_visitor(plan, params_restore_visitor, context);
}

static bool
sr_plan_expr_walker_tamplate(Node *node, void *context)
{
    struct QueryParamsContext *qp_context = context;

    FuncExpr *fexpr = (FuncExpr *)node;
    OpExpr *Opexpr = (OpExpr *)node;
    if (node == NULL)
        return false;

    if (IsA(node, OpExpr))
    {

        ListCell *lc;

        foreach (lc, qp_context->optparams)
        {
            struct OpParam *param = lfirst(lc);

            if (Opexpr->location == param->order)
            {
                Opexpr->opfuncid = Opexpr->location;
                // Opexpr->location = param->order;
                Opexpr->opno = 20000;
                if (cachedInfo.log_usage)
                    elog(cachedInfo.log_usage, "sr_plan: Tamplate Optparameter on %d", param->location);
                break;
            }
        }

        //		return false;
    }
    else if (IsA(node, FuncExpr) && fexpr->funcid == cachedInfo.fake_func)
    {

        ListCell *lc;

        foreach (lc, qp_context->params)
        {
            struct QueryParam *param = lfirst(lc);

            if (fexpr->location == param->order)
            {
                // qp_context->travel_p++;
                fexpr->funccollid = fexpr->location;
#if PG_VERSION_NUM >= 130000
                fexpr->args->elements[0].ptr_value = NULL;
#else
                fexpr->args = list_make1(makeConst(23, -1, 0, 4, (Datum)0, false, true));
#endif
                if (cachedInfo.log_usage)
                    elog(cachedInfo.log_usage, "sr_plan:Tamplate parameter on %d", param->location);
                fexpr->location = param->order;
                break;
            }
        }

        //		return false;
    }

    return expression_tree_walker(node, sr_plan_expr_walker_tamplate, context);
}

static void
plan_template_visitor(Plan *plan, void *context)
{
    expression_tree_walker((Node *)plan->qual, sr_plan_expr_walker_tamplate, context);
    expression_tree_walker((Node *)plan->targetlist, sr_plan_expr_walker_tamplate, context);
}
static void
get_template_plan(void *context, Plan *plan)
{
    plan_tree_visitor(plan, plan_template_visitor, context);
}

static void
collect_indexid_visitor(Plan *plan, void *context)
{
    struct IndexIds *index_ids = context;
    if (plan == NULL)
        return;

    if (IsA(plan, IndexScan))
    {
        IndexScan *scan = (IndexScan *)plan;
        index_ids->ids = lappend_oid(index_ids->ids, scan->indexid);
    }

    if (IsA(plan, IndexOnlyScan))
    {
        IndexOnlyScan *scan = (IndexOnlyScan *)plan;
        index_ids->ids = lappend_oid(index_ids->ids, scan->indexid);
    }

    if (IsA(plan, BitmapIndexScan))
    {
        BitmapIndexScan *scan = (BitmapIndexScan *)plan;
        index_ids->ids = lappend_oid(index_ids->ids, scan->indexid);
    }
}

static void
collect_indexid(void *context, Plan *plan)
{
    plan_tree_visitor(plan, collect_indexid_visitor, context);
}
// this function do not have count detect
static PlannedStmt *
lookup_plan_by_query_hash(Snapshot snapshot, Relation sr_index_rel,
                          Relation sr_plans_heap, ScanKey key,
                          void *context,
                          int index,
                          char **queryString)
{
    int counter = 0;
    PlannedStmt *pl_stmt = NULL;
    HeapTuple htup;
    IndexScanDesc query_index_scan;
#if PG_VERSION_NUM >= 120000
    TupleTableSlot *slot = table_slot_create(sr_plans_heap, NULL);
#endif

    query_index_scan = index_beginscan(sr_plans_heap, sr_index_rel, snapshot, 1, 0);
    index_rescan(query_index_scan, key, 1, NULL, 0);

#if PG_VERSION_NUM >= 120000
    while (index_getnext_slot(query_index_scan, ForwardScanDirection, slot))
#else
    while ((htup = index_getnext(query_index_scan, ForwardScanDirection)) != NULL)
#endif
    {
        Datum search_values[Anum_sr_attcount];
        bool search_nulls[Anum_sr_attcount];
#if PG_VERSION_NUM >= 120000
        bool shouldFree;

        htup = ExecFetchSlotHeapTuple(slot, false, &shouldFree);
        Assert(!shouldFree);
#endif

        heap_deform_tuple(htup, sr_plans_heap->rd_att,
                          search_values, search_nulls);

        /* Check enabled field or index */
        counter++;
        if ((index > 0 && index == counter) ||
            (index == 0 && DatumGetBool(search_values[Anum_sr_enable - 1])))
        {
            char *out = TextDatumGetCString(DatumGetTextP((search_values[Anum_sr_plan - 1])));
            pl_stmt = stringToNode(out);

            if (queryString)
                *queryString = TextDatumGetCString(
                    DatumGetTextP((search_values[Anum_sr_query - 1])));

            if (context)
                execute_for_plantree(pl_stmt, restore_params, context);

            break;
        }
    }

    index_endscan(query_index_scan);
#if PG_VERSION_NUM >= 120000
    ExecDropSingleTupleTableSlot(slot);
#endif
    return pl_stmt;
}

List *lookup_plan_by_query_hash_list(MemoryContext tmpctx, Snapshot snapshot, Relation sr_index_rel,
                                     Relation sr_plans_heap, ScanKey key,
                                     void *context,
                                     int index,
                                     char **queryString, int *count)
{

    List *plan_list = NULL;
    PlannedStmt *pl_stmt = NULL;
    HeapTuple htup;
    IndexScanDesc query_index_scan;

#if PG_VERSION_NUM >= 120000
    TupleTableSlot *slot = table_slot_create(sr_plans_heap, NULL);
#endif

    query_index_scan = index_beginscan(sr_plans_heap, sr_index_rel, snapshot, 1, 0);
    index_rescan(query_index_scan, key, 1, NULL, 0);

#if PG_VERSION_NUM >= 120000
    while (index_getnext_slot(query_index_scan, ForwardScanDirection, slot))
#else
    while ((htup = index_getnext(query_index_scan, ForwardScanDirection)) != NULL)
#endif
    {
        Datum search_values[Anum_sr_attcount];
        bool search_nulls[Anum_sr_attcount];
#if PG_VERSION_NUM >= 120000
        bool shouldFree;

        htup = ExecFetchSlotHeapTuple(slot, false, &shouldFree);
        Assert(!shouldFree);
#endif

        heap_deform_tuple(htup, sr_plans_heap->rd_att,
                          search_values, search_nulls);

        /* Check enabled field or index */
        if (DatumGetInt32(search_values[Anum_sr_query_count - 1]) > *count)
            *count = DatumGetInt32(search_values[Anum_sr_query_count - 1]);
        if (DatumGetBool(search_values[Anum_sr_enable - 1]) && DatumGetInt32(search_values[Anum_sr_query_count - 1]) > sr_count)
        {
            char *out = TextDatumGetCString(DatumGetTextP((search_values[Anum_sr_plan - 1])));
            pl_stmt = stringToNode(out);
            execute_for_plantree(pl_stmt, restore_params, context);
            plan_list = lappend(plan_list, pl_stmt);
        }
    }
    index_endscan(query_index_scan);
    MemoryContext oldctx = CurrentMemoryContext;
    MemoryContextSwitchTo(tmpctx);
    plan_list = copyObject((List *)plan_list);
    MemoryContextSwitchTo(oldctx);
    return plan_list;
#if PG_VERSION_NUM >= 120000
    ExecDropSingleTupleTableSlot(slot);
#endif
}
void traverseRTable(Query *query, bool *flag)
{
    ListCell *lc;

    foreach (lc, query->rtable)
    {
        RangeTblEntry *rte = (RangeTblEntry *)lfirst(lc);

        if (rte->rtekind == RTE_RELATION)
        {
            char *schemaName = get_namespace_name(get_rel_namespace(rte->relid));
            if (schemaName != NULL && strcmp(schemaName, "pg_catalog") == 0)
            {
                *flag = true;
                return;
            }
        }
        else if (rte->rtekind == RTE_SUBQUERY)
        {
            // Recursively traverse the rtable of the subquery
            traverseRTable(rte->subquery, flag);
        }
    }
}
/* planner_hook */
static PlannedStmt *
#if PG_VERSION_NUM >= 130000
sr_planner(Query *parse, const char *query_string, int cursorOptions, ParamListInfo boundParams)
#else
sr_planner(Query *parse, int cursorOptions, ParamListInfo boundParams)
#endif
{
    Datum query_hash;
    Relation sr_plans_heap,
        sr_index_rel;
    HeapTuple tuple;
    char *plan_text;
    Snapshot snapshot;
    ScanKeyData key;
    bool found;
    Datum plan_hash;
    IndexScanDesc query_index_scan;
    PlannedStmt *pl_stmt = NULL;
    LOCKMODE heap_lock = AccessShareLock;
    struct QueryParamsContext qp_context = {true, -1000, -2000, NULL, NULL};
    PlannedStmt *copy_plan = NULL;
    PlannedStmt *tmp_plan = NULL;
    MemoryContext tmpctx, oldctx;
    List *plan_list = NULL;
    ListCell *plancell = NULL;
    StringInfo plan_jsons = makeStringInfo();
    char *syc_sign = "SiGN#";
    char *syc_end = "e#nd";
    int tmp_query_count = 0;
#if PG_VERSION_NUM >= 120000
    TupleTableSlot *
        slot;
#endif
    static int level = 0;

    level++;

#if PG_VERSION_NUM >= 130000
#define call_standard_planner() \
    (srplan_planner_hook_next ? srplan_planner_hook_next(parse, query_string, cursorOptions, boundParams) : standard_planner(parse, query_string, cursorOptions, boundParams))
#else
#define call_standard_planner() \
    (srplan_planner_hook_next ? srplan_planner_hook_next(parse, cursorOptions, boundParams) : standard_planner(parse, cursorOptions, boundParams))
#endif

    /* Only save plans for SELECT commands */
    bool flag = false;
    traverseRTable(parse, &flag);
    if (flag)
    {
        pl_stmt = call_standard_planner();
        level--;
        return pl_stmt;
    }

    // if (parse->commandType != CMD_SELECT || !cachedInfo.enabled || cachedInfo.explain_query)
    if (parse->commandType != CMD_SELECT || !cachedInfo.enabled)
    {
        pl_stmt = call_standard_planner();
        level--;
        return pl_stmt;
    }

    /* Set extension Oid if needed */
    if (cachedInfo.schema_oid == InvalidOid)
    {
        if (!init_sr_plan())
        {
            /* Just call standard_planner() if schema doesn't exist. */
            pl_stmt = call_standard_planner();
            level--;
            return pl_stmt;
        }
    }

    if (cachedInfo.schema_oid == InvalidOid || cachedInfo.sr_plans_oid == InvalidOid)
    {
        /* Just call standard_planner() if schema doesn't exist. */
        pl_stmt = call_standard_planner();
        level--;
        return pl_stmt;
    }
    // char *testsql = "((web_sales.ws_sold_date_sk = 123.11) AND (c.c_customer_sk = web_sales.ws_bill_customer_sk))";
    // int testnum = 0;
    // JoinCond *jj = GetJoinConds(testsql, &testnum, CurrentMemoryContext);

    //   StrHashMap *Hmap = create_str_hash_map();

    /* Make list with all _p functions and his position */
    sr_query_walker((Query *)parse, &qp_context);
    query_hash = get_query_hash(parse);
    // qp_context.travel_o = 12000;
    // qp_context.travel_p = 13000;
    ScanKeyInit(&key, 1, BTEqualStrategyNumber, F_INT4EQ, query_hash);

    /* Try to find already planned statement */
    heap_lock = AccessShareLock;
#if PG_VERSION_NUM >= 130000
    sr_plans_heap = table_open(cachedInfo.sr_plans_oid, heap_lock);
#else
    sr_plans_heap = heap_open(cachedInfo.sr_plans_oid, heap_lock);
#endif
    sr_index_rel = index_open(cachedInfo.sr_index_oid, heap_lock);

    qp_context.collect = false;
    snapshot = RegisterSnapshot(GetLatestSnapshot());
    int conn_fd;
    conn_fd = connect_to_ML(ML_host, ML_port);
    if (conn_fd < 0)
    {
        elog(WARNING, "Unable to connect to ML server. ");
    }
    if (ML_enabled && conn_fd >= 0)
    {
        int plan_order = 0;
        tmpctx = CurrentMemoryContext;
        plan_list = lookup_plan_by_query_hash_list(tmpctx, snapshot, sr_index_rel, sr_plans_heap,
                                                   &key, &qp_context, 0, NULL, &tmp_query_count);
        if (list_length(plan_list) != 0)
        {

            foreach (plancell, plan_list)
            {
                PlannedStmt *templan = (PlannedStmt *)lfirst(plancell);
                // char *tmp_plan_json = get_json_plan(templan);
                char *tmp_plan_json = get_json_plan_cost(templan);
                appendStringInfo(plan_jsons, tmp_plan_json);
                appendStringInfo(plan_jsons, syc_sign);
            }
            // send json to ml
            appendStringInfo(plan_jsons, syc_end);
            write_all_to_socket(conn_fd, plan_jsons->data);
            shutdown(conn_fd, SHUT_WR);

            // get plan order
            if (read(conn_fd, &plan_order, sizeof(int)) != sizeof(int))
            {
                elog(WARNING, "ML server return wrong value");
                plan_order = 0;
            }
            shutdown(conn_fd, SHUT_RDWR);
            if (plan_order >= list_length(plan_list))
            {
                plan_order = 0;
                elog(WARNING, "ML server return wrong value that over list len");
            }
            pl_stmt = (PlannedStmt *)list_nth(plan_list, plan_order);
        }
    }
    else
    {
        tmpctx = CurrentMemoryContext;
        plan_list = lookup_plan_by_query_hash_list(tmpctx, snapshot, sr_index_rel, sr_plans_heap,
                                                   &key, &qp_context, 0, NULL, &tmp_query_count);
        if (list_length(plan_list) != 0)
            pl_stmt = (PlannedStmt *)list_nth(plan_list, 0);
    }
    if (pl_stmt != NULL)
    {
        level--;
        if (cachedInfo.log_usage > 0)
            elog(cachedInfo.log_usage, "sr_plan: cached plan was used for query: %s", cachedInfo.query_text);

        goto cleanup;
    }

    if (!cachedInfo.write_mode || level > 1)
    {
        /* quick way out if not in write mode */
        pl_stmt = call_standard_planner();
        level--;
        goto cleanup;
    }

    /* close and get AccessExclusiveLock */
    UnregisterSnapshot(snapshot);
    index_close(sr_index_rel, heap_lock);
#if PG_VERSION_NUM >= 130000
    table_close(sr_plans_heap, heap_lock);
#else
    heap_close(sr_plans_heap, heap_lock);
#endif

    heap_lock = AccessExclusiveLock;
#if PG_VERSION_NUM >= 130000
    sr_plans_heap = table_open(cachedInfo.sr_plans_oid, heap_lock);
#else
    sr_plans_heap = heap_open(cachedInfo.sr_plans_oid, heap_lock);
#endif
    sr_index_rel = index_open(cachedInfo.sr_index_oid, heap_lock);

    /* recheck plan in index */
    snapshot = RegisterSnapshot(GetLatestSnapshot());
    //    pl_stmt = lookup_plan_by_query_hash(snapshot, sr_index_rel, sr_plans_heap,
    // &key, &qp_context, 0, NULL);
    if (pl_stmt != NULL)
    {
        level--;
        goto cleanup;
    }

    /* from now on we use this new plan */
    pl_stmt = call_standard_planner();
    level--;
    ///////////////////////////////////////
    // modify*
    tmpctx = AllocSetContextCreate(CurrentMemoryContext,
                                   "temporary context",
                                   ALLOCSET_DEFAULT_SIZES);

    oldctx = CurrentMemoryContext;

    if (tmp_query_count < sr_count && tmp_query_count > 0)
    {
        query_index_scan = index_beginscan(sr_plans_heap, sr_index_rel,
                                           snapshot, 1, 0);
        index_rescan(query_index_scan, &key, 1, NULL, 0);
        for (;;)
        {
            HeapTuple htup;
            HeapTuple newhtup;
            Datum search_values[Anum_sr_attcount];
            bool search_nulls[Anum_sr_attcount];
            bool doreplace[Anum_sr_attcount];
            MemSet(search_nulls, 0, sizeof(search_nulls));
            MemSet(doreplace, 0, sizeof(doreplace));
            ItemPointer tid = index_getnext_tid(query_index_scan, ForwardScanDirection);
            if (tid == NULL)
                break;

            htup = index_fetch_heap(query_index_scan);
            if (htup == NULL)
                break;

            heap_deform_tuple(htup, sr_plans_heap->rd_att,
                              search_values, search_nulls);

            /* Detect full plan duplicate */
            if (DatumGetInt32(search_values[Anum_sr_query_count - 1]) < sr_count)
            {
                search_values[Anum_sr_query_count - 1] = (Int32GetDatum(DatumGetInt32(search_values[Anum_sr_query_count - 1]) + 1));
                doreplace[Anum_sr_query_count - 1] = true;
                newhtup = heap_modify_tuple(htup, sr_plans_heap->rd_att, search_values, search_nulls, doreplace);
                simple_heap_update(sr_plans_heap, tid, newhtup);
            }
        }
        index_endscan(query_index_scan);
    }
    else
    {

        copy_plan = copyObject((PlannedStmt *)pl_stmt);
        execute_for_plantree(copy_plan, get_template_plan, &qp_context);
        copy_plan->stmt_len = 0;
        tmp_plan = pl_stmt;
        pl_stmt = copy_plan;
        copy_plan = tmp_plan;
        ////////////////////////////////
        plan_text = nodeToString_sr(pl_stmt);
        plan_hash = hash_any((unsigned char *)plan_text, strlen(plan_text));

        /*
         * Try to find existing plan for this query and skip addding it
         * to prevent duplicates.
         */
        query_index_scan = index_beginscan(sr_plans_heap, sr_index_rel,
                                           snapshot, 1, 0);
        index_rescan(query_index_scan, &key, 1, NULL, 0);
#if PG_VERSION_NUM >= 120000
        slot = table_slot_create(sr_plans_heap, NULL);
#endif
        found = false;
        for (;;)
        {
            HeapTuple htup;
            Datum search_values[Anum_sr_attcount];
            bool search_nulls[Anum_sr_attcount];
#if PG_VERSION_NUM >= 120000
            bool shouldFree;

            if (!index_getnext_slot(query_index_scan, ForwardScanDirection, slot))
                break;

            htup = ExecFetchSlotHeapTuple(slot, false, &shouldFree);
            Assert(!shouldFree);
#else
            ItemPointer tid = index_getnext_tid(query_index_scan, ForwardScanDirection);
            if (tid == NULL)
                break;

            htup = index_fetch_heap(query_index_scan);
            if (htup == NULL)
                break;
#endif
            heap_deform_tuple(htup, sr_plans_heap->rd_att,
                              search_values, search_nulls);

            /* Detect full plan duplicate */
            if (DatumGetInt32(search_values[Anum_sr_plan_hash - 1]) == DatumGetInt32(plan_hash))
            {
                found = true;
                break;
            }
        }
        index_endscan(query_index_scan);
#if PG_VERSION_NUM >= 120000
        ExecDropSingleTupleTableSlot(slot);
#endif
        if (!found)
        {
            struct IndexIds index_ids = {NIL};

            Relation reloids_index_rel;
            Relation index_reloids_index_rel;

            ArrayType *reloids = NULL;
            ArrayType *index_reloids = NULL;
            Datum values[Anum_sr_attcount];
            bool nulls[Anum_sr_attcount];
            int reloids_len = list_length(pl_stmt->relationOids);
            int datum_q_count = sr_count + 1;
            /* prepare indexes */
            reloids_index_rel = index_open(cachedInfo.reloids_index_oid, heap_lock);
            index_reloids_index_rel = index_open(cachedInfo.index_reloids_index_oid, heap_lock);

            MemSet(nulls, 0, sizeof(nulls));
            if (tmp_query_count == 0)
            {
                values[Anum_sr_plan_hash - 1] = Int64GetDatum(0);
                values[Anum_sr_plan - 1] = CStringGetTextDatum("Nothing");
                values[Anum_sr_query_count - 1] = Int64GetDatum(1);
            }
            else
            {
                values[Anum_sr_plan_hash - 1] = plan_hash;
                values[Anum_sr_plan - 1] = CStringGetTextDatum(plan_text);
                values[Anum_sr_query_count - 1] = Int64GetDatum(datum_q_count);
            }
            values[Anum_sr_query_hash - 1] = query_hash;
            values[Anum_sr_query_id - 1] = Int64GetDatum(parse->queryId);
            values[Anum_sr_query - 1] = CStringGetTextDatum(cachedInfo.query_text);
            values[Anum_sr_enable - 1] = BoolGetDatum(false);
            values[Anum_sr_reloids - 1] = (Datum)0;
            values[Anum_sr_index_reloids - 1] = (Datum)0;
            MemoryContext _tm = MemoryContextSwitchTo(tmpctx);

            /* save related oids */
            if (reloids_len)
            {
                int pos;
                ListCell *lc;
                Datum *reloids_arr = palloc(sizeof(Datum) * reloids_len);

                pos = 0;
                foreach (lc, pl_stmt->relationOids)
                {
                    reloids_arr[pos] = ObjectIdGetDatum(lfirst_oid(lc));
                    pos++;
                }
                reloids = construct_array(reloids_arr, reloids_len, OIDOID,
                                          sizeof(Oid), true, 'i');
                values[Anum_sr_reloids - 1] = PointerGetDatum(reloids);

                pfree(reloids_arr);
            }
            else
                nulls[Anum_sr_reloids - 1] = true;

            /* saved related index oids */
            execute_for_plantree(pl_stmt, collect_indexid, (void *)&index_ids);
            if (list_length(index_ids.ids))
            {
                int len = list_length(index_ids.ids);
                int pos;
                ListCell *lc;
                Datum *ids_arr = palloc(sizeof(Datum) * len);

                pos = 0;
                foreach (lc, index_ids.ids)
                {
                    ids_arr[pos] = ObjectIdGetDatum(lfirst_oid(lc));
                    pos++;
                }
                index_reloids = construct_array(ids_arr, len, OIDOID,
                                                sizeof(Oid), true, 'i');
                values[Anum_sr_index_reloids - 1] = PointerGetDatum(index_reloids);

                pfree(ids_arr);
            }
            else
                nulls[Anum_sr_index_reloids - 1] = true;

            tuple = heap_form_tuple(sr_plans_heap->rd_att, values, nulls);
            simple_heap_insert(sr_plans_heap, tuple);

            if (cachedInfo.log_usage)
                elog(cachedInfo.log_usage, "sr_plan: saved plan for %s", cachedInfo.query_text);

            index_insert_compat(sr_index_rel,
                                values, nulls,
                                &(tuple->t_self),
                                sr_plans_heap,
                                UNIQUE_CHECK_NO);

            if (reloids)
            {
                index_insert_compat(reloids_index_rel,
                                    &values[Anum_sr_reloids - 1],
                                    &nulls[Anum_sr_reloids - 1],
                                    &(tuple->t_self),
                                    sr_plans_heap,
                                    UNIQUE_CHECK_NO);
            }

            if (index_reloids)
            {
                index_insert_compat(index_reloids_index_rel,
                                    &values[Anum_sr_index_reloids - 1],
                                    &nulls[Anum_sr_index_reloids - 1],
                                    &(tuple->t_self),
                                    sr_plans_heap,
                                    UNIQUE_CHECK_NO);
            }

            index_close(reloids_index_rel, heap_lock);
            index_close(index_reloids_index_rel, heap_lock);

            /* Make changes visible */
            CommandCounterIncrement();
            MemoryContextSwitchTo(_tm);
        }
    }

cleanup:
    UnregisterSnapshot(snapshot);

    index_close(sr_index_rel, heap_lock);
#if PG_VERSION_NUM >= 130000
    table_close(sr_plans_heap, heap_lock);
#else
    heap_close(sr_plans_heap, heap_lock);
#endif
    if (cachedInfo.write_mode && tmp_plan != NULL)
    {
        MemoryContextSwitchTo(oldctx);
        MemoryContextDelete(tmpctx);
    }

    if (tmp_plan != NULL)
    {
        pl_stmt = tmp_plan;
    }
    get_json_plan_cost(pl_stmt);
    return pl_stmt;
}

static bool
sr_query_walker(Query *node, void *context)
{
    if (node == NULL)
        return false;

    // check for nodes that special work is required for, eg:
    if (IsA(node, FromExpr))
        return sr_query_expr_walker((Node *)node, context);

    // for any node type not specially processed, do:
    if (IsA(node, Query))
        return query_tree_walker(node, sr_query_walker, context, 0);

    return false;
}

static bool
sr_query_expr_walker(Node *node, void *context)
{
    struct QueryParamsContext *qp_context = context;

    FuncExpr *fexpr = (FuncExpr *)node;
    OpExpr *Opexpr = (OpExpr *)node;
    if (node == NULL)
        return false;
    // Warning	bug exists
    if (IsA(node, OpExpr))
    {
        if (qp_context->collect)
        {
            struct OpParam *param = (struct OpParam *)palloc(sizeof(struct OpParam));
            param->location = Opexpr->location;
            param->opno = Opexpr->opno;
            param->opfuncid = Opexpr->opfuncid;
            // 注意opfuncid用于执行阶段，因此在此暂时修改不会对规划有影响，但是opno不能随意修改，会用在优化阶段
            // Opexpr->opfuncid = qp_context->travel_o;
            Opexpr->location = qp_context->travel_o;
            param->order = qp_context->travel_o;
            qp_context->travel_o--;

            if (cachedInfo.log_usage)
                elog(cachedInfo.log_usage, "sr_plan: collected Opparameter on %d", param->location);

            qp_context->optparams = lappend(qp_context->optparams, param);
        }
        else
        {
            ListCell *lc;

            foreach (lc, qp_context->optparams)
            {
                struct OpParam *param = lfirst(lc);

                if (Opexpr->opfuncid == param->order)
                {
                    Opexpr->opfuncid = param->opfuncid;
                    Opexpr->location = param->location;
                    Opexpr->opno = param->opno;

                    if (cachedInfo.log_usage)
                        elog(cachedInfo.log_usage, "sr_plan: restored Optparameter on %d", param->location);

                    break;
                }
            }
        }

        //		return false;
    }
    if (IsA(node, FuncExpr) && fexpr->funcid == cachedInfo.fake_func)
    {
        if (qp_context->collect)
        {
            struct QueryParam *param = (struct QueryParam *)palloc(sizeof(struct QueryParam));
            param->location = fexpr->location;
#if PG_VERSION_NUM >= 130000
            param->node = fexpr->args->elements[0].ptr_value;
#else
            // param->node = fexpr->args->head->data.ptr_value;
            param->node = fexpr->args;
#endif
            param->funccollid = fexpr->funccollid;

            // 标记位
            //	param->order = qp_context
            // funccollid 用于指定函数结果的排序规则 实际上不应该替换 但由于_p仅简单返回输入参数，因此可使用其暂时保存标志
            //

            if (cachedInfo.log_usage)
                elog(cachedInfo.log_usage, "sr_plan: collected parameter on %d", param->location);
            param->order = qp_context->travel_p;
            fexpr->location = qp_context->travel_p;
            qp_context->travel_p--;
            qp_context->params = lappend(qp_context->params, param);
        }
        else
        {
            ListCell *lc;

            foreach (lc, qp_context->params)
            {
                struct QueryParam *param = lfirst(lc);

                if (fexpr->funccollid == param->order)
                {
                    // qp_context->travel_p++;
                    fexpr->funccollid = param->funccollid;
#if PG_VERSION_NUM >= 130000
                    fexpr->args->elements[0].ptr_value = param->node;
#else
                    // fexpr->args->head->data.ptr_value = param->node;
                    fexpr->args = param->node;
#endif
                    if (cachedInfo.log_usage)
                        elog(cachedInfo.log_usage, "sr_plan: restored parameter on %d", param->location);
                    fexpr->location = param->location;
                    break;
                }
            }
        }

        //	return false;
    }
    if (IsA(node, Query))
    {
        return query_tree_walker((Query *)node, sr_query_walker, context, 0);
    }

    return expression_tree_walker(node, sr_query_expr_walker, context);
}
// 用于生成查询模版的hash,这里的node为copy，仅用于生成hash,不会影响原node
static bool
sr_query_fake_const_expr_walker(Node *node, void *context)
{
    FuncExpr *fexpr = (FuncExpr *)node;
    OpExpr *Opexpr = (OpExpr *)node;
    Datum fake_oid;
    if (node == NULL)
        return false;

    if (IsA(node, FuncExpr) && fexpr->funcid == cachedInfo.fake_func)
    {
        Const *fakeconst;
        fexpr->funcresulttype = 0;
        fakeconst = makeConst(23, -1, 0, 4, (Datum)0, false, true);
        fexpr->args = list_make1(fakeconst);
    }

    if (IsA(node, OpExpr))
    {
        // modify*
        // 构造操作符hash 在生成query时替代真实操作符
        // opno表示操作符类型  即使自然语言相同 如 >  在内部也因数据类型而区分
        // opfuncid
        fake_oid = getOptName(Opexpr->opno);
        if (fake_oid != 0)
        {
            Opexpr->opno = fake_oid;
            Opexpr->opfuncid = 0;
        }
    }
    if (IsA(node, Query))
    {
        return query_tree_walker((Query *)node, sr_query_fake_const_walker, context, 0);
    }
    return expression_tree_walker(node, sr_query_fake_const_expr_walker, context);
}

static bool
sr_query_fake_const_walker(Node *node, void *context)
{
    if (node == NULL)
        return false;

    // check for nodes that special work is required for, eg:
    if (IsA(node, FromExpr))
        return sr_query_fake_const_expr_walker(node, context);

    // for any node type not specially processed, do:
    if (IsA(node, Query))
    {
        Query *q = (Query *)node;
        return query_tree_walker(q, sr_query_fake_const_walker, context, 0);
    }

    return false;
}

static Datum
get_query_hash(Query *node)
{
    Datum result;
    Node *copy;
    MemoryContext tmpctx, oldctx;
    int tmplen = 0;
    char *temp;
    tmpctx = AllocSetContextCreate(CurrentMemoryContext,
                                   "temporary context",
                                   ALLOCSET_DEFAULT_SIZES);
    oldctx = MemoryContextSwitchTo(tmpctx);
    tmplen = node->stmt_len;
    // modify*
    // 将query语句的长度归零，防止因模版匹配失败（空格等问题）
    node->stmt_len = 0;
    copy = copyObject((Node *)node);
    node->stmt_len = tmplen;
    sr_query_fake_const_walker(copy, NULL);
    temp = nodeToString_sr(copy);
    result = hash_any((unsigned char *)temp, strlen(temp));
    MemoryContextSwitchTo(oldctx);
    MemoryContextDelete(tmpctx);

    return result;
}

static const struct config_enum_entry log_usage_options[] = {
    {"none", 0, true},
    {"debug", DEBUG2, true},
    {"debug5", DEBUG5, false},
    {"debug4", DEBUG4, false},
    {"debug3", DEBUG3, false},
    {"debug2", DEBUG2, false},
    {"debug1", DEBUG1, false},
    {"log", LOG, false},
    {"info", INFO, true},
    {"notice", NOTICE, false},
    {"warning", WARNING, false},
    {NULL, 0, false}};

void _PG_init(void)
{
    DefineCustomBoolVariable("sr_plan.write_mode",
                             "Save all plans for all queries.",
                             NULL,
                             &cachedInfo.write_mode,
                             false,
                             PGC_SUSET,
                             0,
                             NULL,
                             NULL,
                             NULL);

    DefineCustomBoolVariable("sr_plan.enabled",
                             "Enable sr_plan.",
                             NULL,
                             &cachedInfo.enabled,
                             true,
                             PGC_SUSET,
                             0,
                             NULL,
                             NULL,
                             NULL);
    DefineCustomBoolVariable("ML.enabled",
                             "Enable ML model select plan.",
                             NULL,
                             &ML_enabled,
                             true,
                             PGC_SUSET,
                             0,
                             NULL,
                             NULL,
                             NULL);
    DefineCustomEnumVariable("sr_plan.log_usage",
                             "Log cached plan usage with specified level",
                             NULL,
                             &cachedInfo.log_usage,
                             0,
                             log_usage_options,
                             PGC_USERSET,
                             0,
                             NULL,
                             NULL,
                             NULL);
    DefineCustomStringVariable(
        "ML_host",
        "ML server host",
        NULL,
        &ML_host,
        "localhost",
        PGC_USERSET,
        0,
        NULL,
        NULL,
        NULL);

    DefineCustomIntVariable(
        "ML_port",
        "ML server port",
        NULL,
        &ML_port,
        9381,
        1,
        65536,
        PGC_USERSET,
        0,
        NULL,
        NULL,
        NULL);
    srplan_planner_hook_next = planner_hook;
    planner_hook = &sr_planner;

    srplan_post_parse_analyze_hook_next = post_parse_analyze_hook;
    post_parse_analyze_hook = &sr_analyze;
}

void _PG_fini(void)
{
    /* nothing to do */
}

Datum do_nothing(PG_FUNCTION_ARGS)
{
    PG_RETURN_DATUM(PG_GETARG_DATUM(0));
}

Datum _p(PG_FUNCTION_ARGS)
{
    PG_RETURN_DATUM(PG_GETARG_DATUM(0));
}

/*
 *	Construct the result tupledesc for an EXPLAIN
 */
static TupleDesc
make_tupledesc(ExplainState *es)
{
    TupleDesc tupdesc;
    Oid result_type;

    /* Check for XML format option */
    switch (es->format)
    {
    case EXPLAIN_FORMAT_XML:
        result_type = XMLOID;
        break;
    case EXPLAIN_FORMAT_JSON:
        result_type = JSONOID;
        break;
    default:
        result_type = TEXTOID;
    }

    /* Need a tuple descriptor representing a single TEXT or XML column */
#if PG_VERSION_NUM >= 120000
    tupdesc = CreateTemplateTupleDesc(1);
#else
    tupdesc = CreateTemplateTupleDesc(1, false);
#endif
    TupleDescInitEntry(tupdesc, (AttrNumber)1, "QUERY PLAN", result_type, -1, 0);
    return tupdesc;
}

static PlannedStmt *
lookup_plan_by_query_hash_for_show(Snapshot snapshot, Relation sr_index_rel,
                                   Relation sr_plans_heap, ScanKey key,
                                   void *context,
                                   int index,
                                   char **queryString)
{
    int counter = 0;
    PlannedStmt *pl_stmt = NULL;
    HeapTuple htup;
    IndexScanDesc query_index_scan;
#if PG_VERSION_NUM >= 120000
    TupleTableSlot *slot = table_slot_create(sr_plans_heap, NULL);
#endif

    query_index_scan = index_beginscan(sr_plans_heap, sr_index_rel, snapshot, 1, 0);
    index_rescan(query_index_scan, key, 1, NULL, 0);

#if PG_VERSION_NUM >= 120000
    while (index_getnext_slot(query_index_scan, ForwardScanDirection, slot))
#else
    while ((htup = index_getnext(query_index_scan, ForwardScanDirection)) != NULL)
#endif
    {
        Datum search_values[Anum_sr_attcount];
        bool search_nulls[Anum_sr_attcount];
#if PG_VERSION_NUM >= 120000
        bool shouldFree;

        htup = ExecFetchSlotHeapTuple(slot, false, &shouldFree);
        Assert(!shouldFree);
#endif

        heap_deform_tuple(htup, sr_plans_heap->rd_att,
                          search_values, search_nulls);

        /* Check enabled field or index */
        counter++;
        if ((index > 0 && index == counter) ||
            (index == 0 && DatumGetBool(search_values[Anum_sr_enable - 1])))
        {
            char *out = TextDatumGetCString(DatumGetTextP((search_values[Anum_sr_plan - 1])));
            //	char *query = TextDatumGetCString(DatumGetTextP((search_values[Anum_sr_query - 1])));

            pl_stmt = stringToNode(out);

            if (queryString)
            {
                *queryString = TextDatumGetCString(
                    DatumGetTextP((search_values[Anum_sr_query - 1])));

                ListCell *parsetree_item;
                List *parsetree_list = pg_parse_query(*queryString);

                foreach (parsetree_item, parsetree_list)
                {
                    RawStmt *parsetree = lfirst_node(RawStmt, parsetree_item);
                    List *querytree_list;
                    querytree_list = pg_analyze_and_rewrite(parsetree, *queryString,
                                                            NULL, 0, NULL);
                    ListCell *query_list;
                    foreach (query_list, querytree_list)
                    {
                        Query *query = lfirst_node(Query, query_list);
                        struct QueryParamsContext qp_context = {true, 12000, 13000, NULL, NULL};

                        sr_query_walker(query, &qp_context);
                        qp_context.collect = false;
                        execute_for_plantree(pl_stmt, restore_params, &qp_context);
                    }
                }
            }

            break;
        }
    }

    index_endscan(query_index_scan);
#if PG_VERSION_NUM >= 120000
    ExecDropSingleTupleTableSlot(slot);
#endif
    return pl_stmt;
}

// get json plan from PlannedStmt
char *get_json_plan(PlannedStmt *pl_stmt)
{
    char *queryString = NULL;
    char *json;
    ExplainState *es = NewExplainState();
    es->analyze = false;
    es->costs = true;
    es->verbose = true;
    es->buffers = false;
    es->timing = false;
    es->summary = false;
    es->format = EXPLAIN_FORMAT_JSON;
    ExplainBeginOutput(es);
#if PG_VERSION_NUM >= 130000
    ExplainOnePlan(pl_stmt, NULL, es, queryString, NULL, NULL, NULL, NULL);
#elif PG_VERSION_NUM >= 100000
    ExplainOnePlan(pl_stmt, NULL, es, queryString, NULL, NULL, NULL);
#else
    ExplainOnePlan(pl_stmt, NULL, es, queryString, NULL, NULL);
#endif
    ExplainEndOutput(es);
    json = pstrdup(es->str->data);
    return json;
}
Datum show_plan(PG_FUNCTION_ARGS)
{
    FuncCallContext *funcctx;
    show_plan_funcctx *ctx;

    if (SRF_IS_FIRSTCALL())
    {
        MemoryContext oldcxt;
        PlannedStmt *pl_stmt = NULL;
        LOCKMODE heap_lock = AccessShareLock;
        Relation sr_plans_heap,
            sr_index_rel;
        Snapshot snapshot;
        ScanKeyData key;
        ListCell *lc;
        char *queryString;
        ExplainState *es = NewExplainState();
        uint32 index,
            query_hash = PG_GETARG_INT32(0);
        Relation *rel_array;
        int i;

        funcctx = SRF_FIRSTCALL_INIT();

        if (!PG_ARGISNULL(1))
            index = PG_GETARG_INT32(1); /* show by index or enabled (if 0) */
        else
            index = 0; /* show enabled one */

        es->analyze = false;
        es->costs = true;
        es->verbose = true;
        es->buffers = false;
        es->timing = false;
        es->summary = false;
        es->format = EXPLAIN_FORMAT_TEXT;

        if (!PG_ARGISNULL(2))
        {
            char *p = PG_GETARG_CSTRING(2);

            if (strcmp(p, "text") == 0)
                es->format = EXPLAIN_FORMAT_TEXT;
            else if (strcmp(p, "xml") == 0)
                es->format = EXPLAIN_FORMAT_XML;
            else if (strcmp(p, "json") == 0)
                es->format = EXPLAIN_FORMAT_JSON;
            else if (strcmp(p, "yaml") == 0)
                es->format = EXPLAIN_FORMAT_YAML;
            else
                ereport(ERROR,
                        (errcode(ERRCODE_INVALID_PARAMETER_VALUE),
                         errmsg("unrecognized value for output format \"%s\"", p),
                         errhint("supported formats: 'text', 'xml', 'json', 'yaml'")));
        }

        /* Try to find already planned statement */
#if PG_VERSION_NUM >= 130000
        sr_plans_heap = table_open(cachedInfo.sr_plans_oid, heap_lock);
#else
        sr_plans_heap = heap_open(cachedInfo.sr_plans_oid, heap_lock);
#endif
        sr_index_rel = index_open(cachedInfo.sr_index_oid, heap_lock);

        snapshot = RegisterSnapshot(GetLatestSnapshot());
        ScanKeyInit(&key, 1, BTEqualStrategyNumber, F_INT4EQ, query_hash);
        pl_stmt = lookup_plan_by_query_hash_for_show(snapshot, sr_index_rel, sr_plans_heap,
                                                     &key, NULL, index, &queryString);
        if (pl_stmt == NULL)
            ereport(ERROR,
                    (errcode(ERRCODE_INVALID_PARAMETER_VALUE),
                     errmsg("could not find saved plan")));

        rel_array = palloc(sizeof(Relation) * list_length(pl_stmt->relationOids));
        i = 0;
        foreach (lc, pl_stmt->relationOids)
#if PG_VERSION_NUM >= 130000
            rel_array[i++] = table_open(lfirst_oid(lc), heap_lock);
#else
            rel_array[i++] = heap_open(lfirst_oid(lc), heap_lock);
#endif

        ExplainBeginOutput(es);
#if PG_VERSION_NUM >= 130000
        ExplainOnePlan(pl_stmt, NULL, es, queryString, NULL, NULL, NULL, NULL);
#elif PG_VERSION_NUM >= 100000
        ExplainOnePlan(pl_stmt, NULL, es, queryString, NULL, NULL, NULL);
#else
        ExplainOnePlan(pl_stmt, NULL, es, queryString, NULL, NULL);
#endif
        ExplainEndOutput(es);
        Assert(es->indent == 0);

        UnregisterSnapshot(snapshot);
        index_close(sr_index_rel, heap_lock);
#if PG_VERSION_NUM >= 130000
        table_close(sr_plans_heap, heap_lock);
#else
        heap_close(sr_plans_heap, heap_lock);
#endif

        while (--i >= 0)
#if PG_VERSION_NUM >= 130000
            table_close(rel_array[i], heap_lock);
#else
            heap_close(rel_array[i], heap_lock);
#endif

        oldcxt = MemoryContextSwitchTo(funcctx->multi_call_memory_ctx);

        funcctx->tuple_desc = BlessTupleDesc(make_tupledesc(es));
        funcctx->user_fctx = palloc(sizeof(show_plan_funcctx));
        ctx = (show_plan_funcctx *)funcctx->user_fctx;

        ctx->format = es->format;
        ctx->output = pstrdup(es->str->data);
        MemoryContextSwitchTo(oldcxt);
    }

    funcctx = SRF_PERCALL_SETUP();
    ctx = (show_plan_funcctx *)funcctx->user_fctx;

    /* if there is a string and not an end of string */
    if (ctx->output && *ctx->output)
    {
        HeapTuple tuple;
        Datum values[1];
        bool isnull[1] = {false};

        if (ctx->format != EXPLAIN_FORMAT_TEXT)
        {
            values[0] = PointerGetDatum(cstring_to_text(ctx->output));
            ctx->output = NULL;
        }
        else
        {
            char *txt = ctx->output;
            char *eol;
            int len;

            eol = strchr(txt, '\n');
            if (eol)
            {
                len = eol - txt;
                eol++;
            }
            else
            {
                len = strlen(txt);
                eol = txt + len;
            }

            values[0] = PointerGetDatum(cstring_to_text_with_len(txt, len));
            ctx->output = txt = eol;
        }

        tuple = heap_form_tuple(funcctx->tuple_desc, values, isnull);
        SRF_RETURN_NEXT(funcctx, HeapTupleGetDatum(tuple));
    }

    SRF_RETURN_DONE(funcctx);
}

/*
 * Basic plan tree walker.
 *
 * 'visitor' is applied right before return.
 */
static void
plan_tree_visitor(Plan *plan,
                  void (*visitor)(Plan *plan, void *context),
                  void *context)
{
    ListCell *l;

    if (plan == NULL)
        return;

    check_stack_depth();

    /* Plan-type-specific fixes */
    switch (nodeTag(plan))
    {
    case T_SubqueryScan:
        plan_tree_visitor(((SubqueryScan *)plan)->subplan, visitor, context);
        break;

    case T_CustomScan:
        foreach (l, ((CustomScan *)plan)->custom_plans)
            plan_tree_visitor((Plan *)lfirst(l), visitor, context);
        break;

    case T_ModifyTable:
        foreach (l, ((ModifyTable *)plan)->plans)
            plan_tree_visitor((Plan *)lfirst(l), visitor, context);
        break;

    case T_Append:
        foreach (l, ((Append *)plan)->appendplans)
            plan_tree_visitor((Plan *)lfirst(l), visitor, context);
        break;

    case T_MergeAppend:
        foreach (l, ((MergeAppend *)plan)->mergeplans)
            plan_tree_visitor((Plan *)lfirst(l), visitor, context);
        break;

    case T_BitmapAnd:
        foreach (l, ((BitmapAnd *)plan)->bitmapplans)
            plan_tree_visitor((Plan *)lfirst(l), visitor, context);
        break;

    case T_BitmapOr:
        foreach (l, ((BitmapOr *)plan)->bitmapplans)
            plan_tree_visitor((Plan *)lfirst(l), visitor, context);
        break;

    default:
        break;
    }

    plan_tree_visitor(plan->lefttree, visitor, context);
    plan_tree_visitor(plan->righttree, visitor, context);

    /* Apply visitor to the current node */
    visitor(plan, context);
}

static void
execute_for_plantree(PlannedStmt *planned_stmt,
                     void (*proc)(void *context, Plan *plan),
                     void *context)
{
    ListCell *lc;

    proc(context, planned_stmt->planTree);

    foreach (lc, planned_stmt->subplans)
    {
        Plan *subplan = lfirst(lc);
        proc(context, subplan);
    }
}
/////cost model
char *get_json_plan_cost(PlannedStmt *pl_stmt)
{
    char *queryString = NULL;
    char *json;
    ExplainState *es = NewExplainState();
    es->analyze = false;
    es->costs = true;
    es->verbose = true;
    es->buffers = false;
    es->timing = false;
    es->summary = false;
    es->format = EXPLAIN_FORMAT_JSON;
    ExplainBeginOutput(es);
#if PG_VERSION_NUM >= 130000
    ExplainOnePlan(pl_stmt, NULL, es, queryString, NULL, NULL, NULL, NULL);
#elif PG_VERSION_NUM >= 100000
    ExplainOnePlan(pl_stmt, NULL, es, queryString, NULL, NULL, NULL);
#else
    ExplainOnePlan(pl_stmt, NULL, es, queryString, NULL, NULL);
#endif
    ExplainEndOutput(es);
    json = pstrdup(es->str->data);
    cJSON *cjson = cJSON_Parse(json);
    StrHashMap *Hmap = create_str_hash_map();
    bulidAliasMap(cjson, Hmap);
    processJson(cjson, Hmap);
    char *jsonStr = cJSON_Print(cjson);
    // 释放内存
    cJSON_Delete(cjson);

    return jsonStr;
}

void execOneSubQuery(const char *sql, int *scost, int *tcost, int *rows, int *width)
{
    RawStmt *c_parsetree = lfirst_node(RawStmt, list_head(pg_parse_query(sql)));
    List *c_querytree_list;
    c_querytree_list = pg_analyze_and_rewrite(c_parsetree, sql,
                                              NULL, 0, NULL);
    Query *c_query = lfirst_node(Query, list_head(c_querytree_list));
    PlannedStmt *c_plan = standard_planner(c_query, CURSOR_OPT_PARALLEL_OK, NULL);
    *scost = c_plan->planTree->startup_cost;
    *tcost = c_plan->planTree->total_cost;
    *rows = c_plan->planTree->plan_rows;
    *width = c_plan->planTree->plan_width;
}
const char *scanType[] = {"Seq Scan", "Index Scan", "Index Only Scan", "Bitmap Index Scan", "Tid Scan"};
const char *scanGUC[] = {"enable_seqscan", "enable_indexscan", "enable_indexonlyscan", "enable_bitmapscan", "enable_tidscan"};
void setGuc(char *scan_type, const char *sql, int *scost, int *tcost, int *rows, int *width)
{
    // save old value
    int c_save_nestlevel = NewGUCNestLevel();
    int old_value[5] = {0};
    int arraySize = sizeof(scanType) / sizeof(scanType[0]);
    for (int i = 0; i < arraySize; i++)
    {
        if (strcmp(GetConfigOption(scanGUC[i], true, false), "on"))
        {
            old_value[i] = 1;
        }
        else
        {
            old_value[i] = 0;
        }
    }

    for (int i = 0; i < arraySize; i++)
    {
        if (strcmp(scanType[i], scan_type) == 0)
        {
            set_config_option(scanGUC[i], "true", PGC_USERSET, PGC_S_SESSION, GUC_ACTION_SAVE, true, 0, false);
        }
        else if (i == 2)
        {
            if (strcmp(scanType[1], scan_type) == 0)
            {
                set_config_option(scanGUC[2], "true", PGC_USERSET, PGC_S_SESSION, GUC_ACTION_SAVE, true, 0, false);
            }
        }
        else
        {
            set_config_option(scanGUC[i], "false", PGC_USERSET, PGC_S_SESSION, GUC_ACTION_SAVE, true, 0, false);
        }
    }
    // get planstmt
    RawStmt *c_parsetree = lfirst_node(RawStmt, list_head(pg_parse_query(sql)));
    List *c_querytree_list;
    c_querytree_list = pg_analyze_and_rewrite(c_parsetree, sql,
                                              NULL, 0, NULL);
    Query *c_query = lfirst_node(Query, list_head(c_querytree_list));

    PlannedStmt *c_plan = standard_planner(c_query, CURSOR_OPT_PARALLEL_OK, NULL);

    *scost = c_plan->planTree->startup_cost;
    *tcost = c_plan->planTree->total_cost;
    *rows = c_plan->planTree->plan_rows;
    *width = c_plan->planTree->plan_width;
    // reload old guc value
    for (int i = 0; i < arraySize; i++)
    {
        if (old_value[i] == 1)
        {
            set_config_option(scanGUC[i], "true", PGC_USERSET, PGC_S_SESSION, GUC_ACTION_SAVE, true, 0, false);
        }
        else
        {
            set_config_option(scanGUC[i], "false", PGC_USERSET, PGC_S_SESSION, GUC_ACTION_SAVE, true, 0, false);
        }
    }
    AtEOXact_GUC(true, c_save_nestlevel);
    // GetConfigOption(const char *name, bool missing_ok, bool restrict_privileged)

    //  set_config_option("name", "true", PGC_USERSET, PGC_S_SESSION, GUC_ACTION_SAVE, true, 0, false);
}
void precessNode(cJSON *json, cJSON *item, StrHashMap *map, cJSON *relnameForBitmap, cJSON *aliasForBitmap)
{
    char *subsql;

    cJSON *condnode = NULL;
    cJSON *aliname = NULL;
    cJSON *filnode = cJSON_GetObjectItem(json, "Filter");

    cJSON *relname = NULL;
    if (relnameForBitmap != NULL && strcmp(item->valuestring, "Bitmap Index Scan") == 0)
    {
        relname = relnameForBitmap;
    }
    else
    {
        relname = cJSON_GetObjectItem(json, "Relation Name");
    }
    if (aliasForBitmap != NULL && strcmp(item->valuestring, "Bitmap Index Scan") == 0)
    {
        aliname = aliasForBitmap;
    }
    else
    {
        aliname = cJSON_GetObjectItem(json, "Alias");
    }

    if (strcmp(item->valuestring, "Bitmap Heap Scan") == 0)
    {
        condnode = cJSON_GetObjectItem(json, "Recheck Cond");
        cJSON *subnode = cJSON_GetObjectItem(json, "Plans");
        cJSON *Titem = subnode->child->child;
        while (Titem != NULL)
        {
            if (strcmp(Titem->valuestring, "Bitmap Index Scan") == 0)
            {
                precessNode(subnode->child, Titem, map, relname, aliname);
                break;
            }
            Titem = Titem->next;
        }
    }
    else
    {
        condnode = cJSON_GetObjectItem(json, "Index Cond");
    }
    StrHashMap *tmpMap = create_str_hash_map();
    size_t subsql_Len = 0;

    subsql_Len += strlen("select * from ");

    if (condnode != NULL)
    {
        int tmpnum = 0;
        JoinCond *tmpJoinCond = GetJoinConds(condnode->valuestring, &tmpnum, CurrentMemoryContext);
        for (int i = 0; i < tmpnum; i++)
        {
            if (str_hash_map_lookup(map, tmpJoinCond[i].t1) && str_hash_map_lookup(map, tmpJoinCond[i].t2))
            {
                str_hash_map_insert(tmpMap, str_hash_map_lookup(map, tmpJoinCond[i].t1), tmpJoinCond[i].t1);
                str_hash_map_insert(tmpMap, str_hash_map_lookup(map, tmpJoinCond[i].t2), tmpJoinCond[i].t2);
            }
        }
        subsql_Len += strlen(condnode->valuestring);
    }
    if (filnode != NULL)
    {
        subsql_Len += strlen(filnode->valuestring);
    }
    if (aliname != NULL)
    {
        str_hash_map_insert(tmpMap, relname->valuestring, aliname->valuestring);
    }
    else
    {
        str_hash_map_insert(tmpMap, relname->valuestring, "NOALIAS");
    }
    int iter = 0;
    while (iter < tmpMap->size)
    {
        if (strcmp(tmpMap->pairs[iter].value, "NOALIAS"))
        {
            subsql_Len += strlen(tmpMap->pairs[iter].key);
            subsql_Len += strlen(tmpMap->pairs[iter].value);
            subsql_Len += strlen(" as ");
        }
        else
        {
            subsql_Len += strlen(tmpMap->pairs[iter].key);
        }
        subsql_Len += 1; // len of ,
        iter++;
    }
    if (condnode != NULL && filnode != NULL)
    {
        subsql_Len += strlen(" and ");
    }
    if (condnode != NULL || filnode != NULL)
    {
        subsql_Len += strlen(" where ");
    }
    subsql = (char *)palloc(subsql_Len + 10);
    strcpy(subsql, "select * from ");
    iter = 0;
    while (iter < tmpMap->size)
    {
        if (strcmp(tmpMap->pairs[iter].value, "NOALIAS"))
        {

            strcat(subsql, tmpMap->pairs[iter].key);
            strcat(subsql, " as ");
            strcat(subsql, tmpMap->pairs[iter].value);
        }
        else
        {
            strcat(subsql, tmpMap->pairs[iter].key);
        }
        if (iter < tmpMap->size - 1)
        {
            strcat(subsql, ",");
        }
        iter++;
    }
    if (condnode != NULL || filnode != NULL)
    {
        strcat(subsql, " where ");
    }

    if (condnode != NULL)
    {
        strcat(subsql, condnode->valuestring);
    }
    if (condnode != NULL && filnode != NULL)
    {
        strcat(subsql, " and ");
    }
    if (filnode != NULL)
    {
        strcat(subsql, filnode->valuestring);
    }
    strcat(subsql, ";");
    int scost = 0;
    int tcost = 0;
    int rows = 0;
    int width = 0;
    execOneSubQuery(subsql, &scost, &tcost, &rows, &width);
    //   free(subsql);
    cJSON *cnode = cJSON_GetObjectItem(json, "Startup Cost");
    if (cnode)
    {
        cnode->valuedouble = scost;
    }
    cnode = cJSON_GetObjectItem(json, "Total Cost");
    if (cnode)
    {
        cnode->valuedouble = tcost;
    }
    cnode = cJSON_GetObjectItem(json, "Plan Rows");
    if (cnode)
    {
        cnode->valuedouble = rows;
    }
    cnode = cJSON_GetObjectItem(json, "Plan Width");
    if (cnode)
    {
        cnode->valuedouble = width;
    }
}

void processJson(cJSON *json, StrHashMap *map)
{
    if (json->type == cJSON_Object)
    {
        cJSON *item = json->child;
        while (item)
        {

            if (strcmp(item->string, "Node Type") == 0)
            {
                if (strcmp(item->valuestring, "Seq Scan") == 0 || strcmp(item->valuestring, "Index Scan") == 0 ||
                    strcmp(item->valuestring, "Index Only Scan") == 0 || strcmp(item->valuestring, "Bitmap Heap Scan") == 0)
                {
                    precessNode(json, item, map, NULL, NULL);
                }
            }

            // if (strcmp(item->string, "Node Type") == 0)
            // {
            //     if (strcmp(item->valuestring, "Seq Scan") == 0 || strcmp(item->valuestring, "Index Scan") == 0 ||
            //         strcmp(item->valuestring, "Index Only Scan") == 0 || strcmp(item->valuestring, "Bitmap Index Scan") == 0)
            //     {
            //         cJSON *filnode = cJSON_GetObjectItem(json, "Filter");
            //         cJSON *relname = cJSON_GetObjectItem(json, "Relation Name");
            //         cJSON *aliname = cJSON_GetObjectItem(json, "Alias");
            //         char *subsql;
            //         if (relname)
            //         {
            //             if (!filnode)
            //             {
            //                 // no filter
            //                 size_t result_length = strlen("select * from ") + strlen(relname->valuestring) + 1;
            //                 subsql = (char *)palloc(result_length);
            //                 strcpy(subsql, "select * from ");
            //                 strcat(subsql, relname->valuestring);
            //                 //"select * from " "where"
            //             }
            //             else
            //             {
            //                 if (aliname)
            //                 {
            //                     size_t result_length = strlen("select * from ") +
            //                                            strlen(relname->valuestring) + strlen(" as ") +
            //                                            strlen(aliname->valuestring) + strlen(" where ") +
            //                                            strlen(filnode->valuestring) + 1;
            //                     subsql = (char *)palloc(result_length);
            //                     strcpy(subsql, "select * from ");
            //                     strcat(subsql, relname->valuestring);
            //                     strcat(subsql, " as ");
            //                     strcat(subsql, aliname->valuestring);
            //                     strcat(subsql, " where ");
            //                     strcat(subsql, filnode->valuestring);
            //                 }
            //                 else
            //                 {
            //                     size_t result_length = strlen("select * from ") +
            //                                            strlen(relname->valuestring) + strlen(" where ") + strlen(filnode->valuestring) + 1;
            //                     subsql = (char *)palloc(result_length);
            //                     strcpy(subsql, "select * from ");
            //                     strcat(subsql, relname->valuestring);
            //                     strcat(subsql, " where ");
            //                     strcat(subsql, filnode->valuestring);
            //                 }
            //             }
            //         }
            //         int scost = 0;
            //         int tcost = 0;
            //         int rows = 0;
            //         int width = 0;
            //         setGuc(item->valuestring, subsql, &scost, &tcost, &rows, &width);
            //         //   free(subsql);
            //         cJSON *cnode = cJSON_GetObjectItem(json, "Startup Cost");
            //         if (cnode)
            //         {
            //             cnode->valuedouble = scost;
            //         }
            //         cnode = cJSON_GetObjectItem(json, "Total Cost");
            //         if (cnode)
            //         {
            //             cnode->valuedouble = tcost;
            //         }
            //         cnode = cJSON_GetObjectItem(json, "Plan Rows");
            //         if (cnode)
            //         {
            //             cnode->valuedouble = rows;
            //         }
            //         cnode = cJSON_GetObjectItem(json, "Plan Width");
            //         if (cnode)
            //         {
            //             cnode->valuedouble = width;
            //         }
            //     }
            // }

            // 递归处理子节点
            processJson(item, map);
            item = item->next;
        }
    }
    else if (json->type == cJSON_Array)
    {
        cJSON *item = json->child;
        while (item)
        {
            processJson(item, map);
            item = item->next;
        }
    }
}

JoinCond *GetJoinConds(const char *sql, int *num, MemoryContext _tm)
{
    regex_t regex;
    regmatch_t pmatch[5];
    const char *pattern = "([[:alnum:]_]+)\.([[:alnum:]_]+)[[:space:]]*=[[:space:]]*([[:alnum:]_]+)\.([[:alnum:]_]+)";
    int reti = regcomp(&regex, pattern, REG_EXTENDED);
    if (reti)
    {
        fprintf(stderr, "Could not compile regex\n");
        exit(1);
    }

    const char *p = sql;
    JoinCond *join_conds = NULL;
    *num = 0;
    MemoryContext _od = CurrentMemoryContext;
    while (regexec(&regex, p, 5, pmatch, 0) == 0)
    {
        MemoryContextSwitchTo(_tm);
        if (join_conds == NULL)
        {
            join_conds = palloc(sizeof(JoinCond));
        }
        else
        {
            join_conds = repalloc(join_conds, (*num + 1) * sizeof(JoinCond));
        }
        MemoryContextSwitchTo(_od);
        int len = pmatch[1].rm_eo - pmatch[1].rm_so;
        strncpy(join_conds[*num].t1, p + pmatch[1].rm_so, len);
        join_conds[*num].t1[len] = '\0';

        len = pmatch[2].rm_eo - pmatch[2].rm_so;
        strncpy(join_conds[*num].c1, p + pmatch[2].rm_so, len);
        join_conds[*num].c1[len] = '\0';

        len = pmatch[3].rm_eo - pmatch[3].rm_so;
        strncpy(join_conds[*num].t2, p + pmatch[3].rm_so, len);
        join_conds[*num].t2[len] = '\0';

        len = pmatch[4].rm_eo - pmatch[4].rm_so;
        strncpy(join_conds[*num].c2, p + pmatch[4].rm_so, len);
        join_conds[*num].c2[len] = '\0';

        (*num)++;
        p += pmatch[0].rm_eo;
    }

    regfree(&regex);
    return join_conds;
}
StrHashMap *create_str_hash_map(void)
{
    StrHashMap *map = (StrHashMap *)palloc(sizeof(StrHashMap));
    map->pairs = (StrPair *)palloc(sizeof(StrPair) * 10);
    map->size = 0;
    map->capacity = 10;
    return map;
}

void str_hash_map_insert(StrHashMap *map, const char *key, const char *value)
{
    for (int i = 0; i < map->size; i++)
    {
        if (strcmp(map->pairs[i].key, key) == 0)
        {
            // Key already exists, update the value
            map->pairs[i].value = pstrdup(value);
            return;
        }
    }

    if (map->size == map->capacity)
    {
        map->capacity *= 2;
        map->pairs = (StrPair *)repalloc(map->pairs, sizeof(StrPair) * map->capacity);
    }
    map->pairs[map->size].key = pstrdup(key);
    map->pairs[map->size].value = pstrdup(value);
    map->size++;
}

const char *str_hash_map_lookup(StrHashMap *map, const char *key)
{
    for (int i = 0; i < map->size; i++)
    {
        if (strcmp(map->pairs[i].key, key) == 0)
        {
            return map->pairs[i].value;
        }
    }
    return NULL;
}

void bulidAliasMap(cJSON *json, StrHashMap *map)
{
    if (json->type == cJSON_Object)
    {
        cJSON *item = json->child;
        while (item)
        {
            if (strcmp(item->string, "Node Type") == 0)
            {
                if (strcmp(item->valuestring, "Seq Scan") == 0 || strcmp(item->valuestring, "Index Scan") == 0 ||
                    strcmp(item->valuestring, "Index Only Scan") == 0)
                {
                    cJSON *relname = cJSON_GetObjectItem(json, "Relation Name");
                    cJSON *aliname = cJSON_GetObjectItem(json, "Alias");
                    if (aliname)
                    {
                        str_hash_map_insert(map, aliname->valuestring, relname->valuestring);
                    }
                    else
                    {
                        str_hash_map_insert(map, relname->valuestring, "NOALIAS");
                    }
                }
            }

            // 递归处理子节点
            bulidAliasMap(item, map);
            item = item->next;
        }
    }
    else if (json->type == cJSON_Array)
    {
        cJSON *item = json->child;
        while (item)
        {
            bulidAliasMap(item, map);
            item = item->next;
        }
    }
}
