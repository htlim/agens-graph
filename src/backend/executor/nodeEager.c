/*
 * nodeEager.c
 *
 * Copyright (c) 2017 by Bitnine Global, Inc.
 *
 * IDENTIFICATION
 *	  src/backend/executor/nodeEager.c
 */

#include "postgres.h"

#include "catalog/pg_type.h"
#include "executor/execdebug.h"
#include "executor/nodeEager.h"
#include "miscadmin.h"
#include "utils/datum.h"
#include "utils/tuplestore.h"

/* hash entry */
typedef struct ModifiedObjEntry
{
	Graphid	key;
	Datum	properties;
} ModifiedObjEntry;


static void
setSlotValueByAttnum(TupleTableSlot *slot, Datum value, int attnum)
{
	AssertArg(attnum > 0 && attnum <= slot->tts_tupleDescriptor->natts);

	slot->tts_values[attnum - 1] = value;
	slot->tts_isnull[attnum - 1] = (value == (Datum) NULL) ? true : false;
}

/* ----------------------------------------------------------------
 *		ExecEager
 *
 *		Eagers tuples from the outer subtree of the node using tupleEager,
 *		which saves the results in a temporary file or memory. After the
 *		initial call, returns a tuple from the file with each call.
 *
 *		Conditions:
 *		  -- none.
 *
 *		Initial States:
 *		  -- the outer child is prepared to return the first tuple.
 * ----------------------------------------------------------------
 */
TupleTableSlot *
ExecEager(EagerState *node)
{
	EState	   *estate;
	ScanDirection dir;
	Tuplestorestate *tuplestorestate;
	TupleTableSlot *result;

	estate = node->ss.ps.state;
	dir = estate->es_direction;
	tuplestorestate = (Tuplestorestate *) node->tuplestorestate;

	/*
	 * If first time through, read all tuples from outer plan and pass them to
	 * tuplestore.c. Subsequent calls just fetch tuples from tuplestore.
	 */
	if (!node->child_done)
	{
		PlanState  *outerNode;
		TupleTableSlot *slot;

		/*
		 * Want to scan subplan in the forward direction.
		 */
		estate->es_direction = ForwardScanDirection;

		/*
		 * Initialize tuplestore module.
		 */
		outerNode = outerPlanState(node);

		tuplestorestate = tuplestore_begin_heap(false, false, work_mem);
		node->tuplestorestate = (void *) tuplestorestate;

		/*
		 * Scan the subplan and feed all the tuples to tuplestore.
		 */
		for (;;)
		{
			ListCell *lc;

			slot = ExecProcNode(outerNode);

			if (TupIsNull(slot))
				break;

			foreach(lc, node->modifiedList)
			{
				int		idx = lfirst_int(lc);
				Oid		type;
				Datum	gid;
				ModifiedObjEntry *entry;

				if (slot->tts_isnull[idx] != 0)
					continue;

				type = slot->tts_tupleDescriptor->attrs[idx]->atttypid;
				if (type == VERTEXOID)
					gid = getVertexIdDatum(slot->tts_values[idx]);
				else if (type == EDGEOID)
					gid = getEdgeIdDatum(slot->tts_values[idx]);
				else if (type == GRAPHPATHOID)
				{
					; //TODO : graph path, check all graph element in a graph path.
				}
				else
					continue;

				entry = hash_search(node->modifiedObject, (void *) &gid, HASH_ENTER, NULL);

				if (node->gwop == GWROP_DELETE)
				{
					entry->properties = (Datum) NULL;
				}
				else if (node->gwop == GWROP_SET)
				{
					if (type == VERTEXOID)
						entry->properties = datumCopy(getVertexPropDatum(slot->tts_values[idx]), false, -1);
					else if (type == EDGEOID)
						entry->properties = datumCopy(getEdgePropDatum(slot->tts_values[idx]), false, -1);
					else if (type == GRAPHPATHOID)
					{
						; //TODO : graph path, check all graph element in a graph path.
					}
					else
						Assert(0);
				}
				else
					Assert(0); // only SET/DELETE is came here
			}

			tuplestore_puttupleslot(tuplestorestate, slot);
		}

		/*
		 * restore to user specified direction
		 */
		estate->es_direction = dir;

		node->child_done = true;
	}

	/*
	 * Get the first or next tuple from tuplestore. Returns NULL if no more
	 * tuples.
	 */
//	slot = node->ss.ss_ScanTupleSlot;


	result = node->ss.ps.ps_ResultTupleSlot;
//	ExecClearTuple(result);

	(void) tuplestore_gettupleslot(tuplestorestate,
								   ScanDirectionIsForward(dir), false, result);

	/* mark slot as containing a virtual tuple */
	if (!TupIsNull(result))
	{
		int i;
		int	natts = result->tts_tupleDescriptor->natts;
		ModifiedObjEntry *entry;

		slot_getallattrs(result);
//		ExecStoreVirtualTuple(result);		// TODO : CHECK

		// TODO : Check graph elements modified.
		for (i=0; i<natts; i++)
		{
			Graphid gid;
			Oid		type;

			if (result->tts_isnull[i] != 0)
				continue;

			// TODO : get graph id
			type = result->tts_tupleDescriptor->attrs[i]->atttypid;

			if (type == VERTEXOID)
				gid = getVertexIdDatum(result->tts_values[i]);
			else if (type == EDGEOID)
				gid = getEdgeIdDatum(result->tts_values[i]);
			else if (type == GRAPHPATHOID)
			{
				continue; //TODO : graph path, check all graph element in a graph path.
			}
			else
				continue;

			entry = hash_search(node->modifiedObject, (void *) &gid, HASH_FIND, NULL);
			if (entry == NULL)
				continue;
			else
			{
				Datum graphelem;
//				MemoryContext oldmctx;
//
//				oldmctx = MemoryContextSwitchTo(node->ss.ps.ps_ExprContext->ecxt_per_tuple_memory);

				if (entry->properties == (Datum) NULL)
				{
					setSlotValueByAttnum(result, (Datum) NULL, i + 1);
				}
				else
				{
					if (type == VERTEXOID)
					{
						graphelem = makeGraphVertexDatum(gid, entry->properties);

						setSlotValueByAttnum(result, graphelem, i + 1);
					}
					else if (type == EDGEOID)
					{
						Datum start, end;

						start = getEdgeStartDatum(result->tts_values[i]);
						end = getEdgeEndDatum(result->tts_values[i]);

						graphelem = makeGraphEdgeDatum(gid, start, end, entry->properties);

						setSlotValueByAttnum(result, graphelem, i + 1);
					}
					else if (type == GRAPHPATHOID)
						continue;
					else
						Assert(0);
				}
//				MemoryContextSwitchTo(oldmctx);
			}
		}

	}

	return result;
}

/* ----------------------------------------------------------------
 *		ExecInitEager
 *
 *		Creates the run-time state information for the Eager node
 *		produced by the planner and initializes its outer subtree.
 * ----------------------------------------------------------------
 */
EagerState *
ExecInitEager(Eager *node, EState *estate, int eflags)
{
	EagerState  *Eagerstate;
	HASHCTL ctl;

	/*
	 * create state structure
	 */
	Eagerstate = makeNode(EagerState);
	Eagerstate->ss.ps.plan = (Plan *) node;
	Eagerstate->ss.ps.state = estate;
	Eagerstate->child_done = false;
	Eagerstate->modifiedList = node->modifylist;
	Eagerstate->gwop = node->gwop;

	/*
	 * tuple table initialization
	 *
	 * Eager nodes only return scan tuples from their child plan.
	 */
	ExecInitResultTupleSlot(estate, &Eagerstate->ss.ps);
	ExecInitScanTupleSlot(estate, &Eagerstate->ss);

	/*
	 * initialize child nodes
	 *
	 * We shield the child node from the need to support REWIND, BACKWARD, or
	 * MARK/RESTORE.
	 */
	eflags &= ~(EXEC_FLAG_REWIND | EXEC_FLAG_BACKWARD | EXEC_FLAG_MARK);

	outerPlanState(Eagerstate) = ExecInitNode(outerPlan(node), estate, eflags);

	/*
	 * initialize tuple type.  no need to initialize projection info because
	 * this node doesn't do projections.
	 */
	ExecAssignResultTypeFromTL(&Eagerstate->ss.ps);
	ExecAssignScanTypeFromOuterPlan(&Eagerstate->ss);
	Eagerstate->ss.ps.ps_ProjInfo = NULL;

	// TODO : init modifyObject htab
	memset(&ctl, 0, sizeof(ctl));
	ctl.keysize = sizeof(Graphid);
	ctl.entrysize = sizeof(ModifiedObjEntry);
	ctl.hcxt = CurrentMemoryContext;

	Eagerstate->modifiedObject =
					hash_create("ModifyGraph SPIPlan cache", 128, &ctl,
								HASH_ELEM | HASH_BLOBS | HASH_CONTEXT);

	return Eagerstate;
}

/* ----------------------------------------------------------------
 *		ExecEndEager(node)
 * ----------------------------------------------------------------
 */
void
ExecEndEager(EagerState *node)
{
	hash_destroy(node->modifiedObject);

	node->modifiedObject = NULL;

	/*
	 * clean out the tuple table
	 */
	ExecClearTuple(node->ss.ss_ScanTupleSlot);
	/* must drop pointer to Eager result tuple */
	ExecClearTuple(node->ss.ps.ps_ResultTupleSlot);

	/*
	 * Release tupleEager resources
	 */
	if (node->tuplestorestate != NULL)
		tuplestore_end(node->tuplestorestate);
	node->tuplestorestate = NULL;

	/*
	 * shut down the subplan
	 */
	ExecEndNode(outerPlanState(node));
}

void
ExecReScanEager(EagerState *node)
{
	if (!node->child_done)
		return;

	/* must drop pointer to Eager result tuple */
	ExecClearTuple(node->ss.ps.ps_ResultTupleSlot);

	/*
	 * If subnode is to be rescanned then we forget previous Eager results; we
	 * have to re-read the subplan.
	 */
	node->child_done = false;
	tuplestore_end(node->tuplestorestate);
	node->tuplestorestate = NULL;
}
