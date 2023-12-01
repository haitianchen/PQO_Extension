# Parameterized Queries in PostgreSQL
Note: Please visit the latest branch to obtain codes. The main branch may be outdated. 
## Rationale

sr_plan looks like Oracle Outline system. It can be used to lock the execution plan. It is necessary if you do not trust the planner or able to form a better plan.

**We partially modified it based on sr_plan to support one-to-many binding of queries to plans.**

## Build and install

```bash
make USE_PGXS=1
make USE_PGXS=1 install
```

and modify your postgres config:

```
shared_preload_libraries = 'sr_plan'
```

## Usage

Install the extension in your database:

```SQL
CREATE EXTENSION sr_plan;
```

If you want to save the query plan is necessary to set the variable:

```SQL
set sr_plan.write_mode = true;
```

Now plans for all subsequent queries will be stored in the table sr_plans.
Don't forget that all queries will be stored including duplicates.

Make an example query:

```SQL
select query_hash from sr_plans where query_hash=10;
```

Disable saving the plan for the query:

```SQL
set sr_plan.write_mode = false;
```

Enable it:

```SQL
update sr_plans set enable=true;
```

After that, the plan for the query will be taken from the sr_plans. In addition sr plan allows you to save a parameterized query plan. In this case, we have some constants in the query are not essential. For the arguments, we use a special function _p (anyelement) for binding.

Suppose we have table a with two columns info and id. we can can bind the parameters using the _p() function.

```SQL
select * from a where id = _p(1);
```

**Note that the _p() function must be specified as an argument when we want to use a template plan.**

## `pg_stat_statements` integration

`sr_plans` table contains `query_id` columns which could be used to make
joins with `pg_stat_statements` tables and views.

Note: in `shared_preload_libraries` list `pg_stat_statements` should be
specified after `sr_plan`.
