#ifndef ___OUTFUNCS_SR_H__
#define ___OUTFUNCS_SR_H__
#include "postgres.h"

#include <ctype.h>
#include "lib/stringinfo.h"
#include "nodes/extensible.h"
#include "nodes/plannodes.h"
#include "nodes/relation.h"
#include "utils/datum.h"
#include "utils/rel.h"

extern char *nodeToString_sr(const void *obj);
#endif
