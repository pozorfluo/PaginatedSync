----------------------------- MODULE PaginatedSync -----------------------------
EXTENDS Naturals, FiniteSets, Functions, Sequences, TLC, SequencesExt, FiniteSetsExt

--------------------------------------------------------------------------------
set ++ e == set \union {e}
set -- e == set \ {e}
--------------------------------------------------------------------------------
CONSTANTS
  Null,
  MaxPageSize,
  MaxTimestamp

ASSUME
  /\ MaxPageSize \in Nat \ {0}
  /\ MaxTimestamp \in Nat
  /\ MaxTimestamp > 2


VARIABLES
  clock,
  log,
  pageSize,
  pulled,
  synced,
  pullCursor,
  syncCursor

vars ==
  << clock, log, pageSize, pulled, synced, pullCursor, syncCursor >>

--------------------------------------------------------------------------------
Timestamps ==
  1..MaxTimestamp

Items ==
  [created : Timestamps, modified : Timestamps]

PullCursors ==
  [lastId : Timestamps, startedAt : Timestamps]

SyncCursors ==
  [lastId : Timestamps, lastModified : Timestamps]
  
ASSUME
  /\ Null \notin PullCursors
  /\ Null \notin SyncCursors
--------------------------------------------------------------------------------
(* Invariant. *)
TypeInvariant ==
  /\ clock \in Nat
  /\ pageSize \in Nat
  /\ log \in SUBSET Items
  /\ pulled \in Seq(Items)
  /\ synced \in Seq(Items)
  /\ pullCursor \in PullCursors ++ Null
  /\ syncCursor \in SyncCursors ++ Null

Init ==
  /\ clock = (MaxTimestamp \div 2) + 1
  /\ pageSize \in 1..MaxPageSize
  /\ log = { [created |-> t, modified |-> t] : t \in 1..(MaxTimestamp \div 2) }
  /\ pulled = <<>>
  /\ synced = <<>>
  /\ pullCursor = Null
  /\ syncCursor = Null

Create ==
  \* Exclude pointless Create before first pull.  
  /\ pulled # <<>>
  /\ clock <= MaxTimestamp
  /\ log' = log ++ [created |-> clock, modified |-> clock]
  /\ clock' = clock + 1
  /\ UNCHANGED << pageSize, pulled, synced, pullCursor, syncCursor >>

Modify ==
  \* Exclude pointless Modify before first pull.  
  /\ pulled # <<>>
  /\ clock <= MaxTimestamp
  /\ \E id \in 1..(clock - 1) :
    /\ log' = { IF i.created = id THEN [created |-> id, modified |-> clock] ELSE i : i \in log }
    /\ clock' = clock + 1
    /\ UNCHANGED << pageSize, pulled, synced, pullCursor, syncCursor >>
  

SortByCreated(a, b) == a.created < b.created
SortByModified(a, b) ==
  a.modified < b.modified \/ (a.modified = b.modified /\ a.created < b.created)

(* Ideal cursor update that cannot fail for now. *)
Pull ==
  /\ syncCursor = Null
  /\ \/ /\ pullCursor = Null
        /\ LET
              sorted == SetToSortSeq(log, SortByCreated)
              length == Len(sorted)
            IN
              \/ /\ length > 0
                 /\ pulled' = pulled \o SubSeq(sorted, 1, Min({pageSize, length}))
                 /\ pullCursor' = [lastId |-> Last(pulled').created, startedAt |-> clock - 1]
                 /\ UNCHANGED << pageSize, log, clock, synced, syncCursor >>
              \/ /\ length = 0
                 /\ syncCursor' = [lastId |-> pullCursor.lastId, lastModified |-> pullCursor.startedAt]
                 /\ UNCHANGED << pageSize, log, clock, synced, pulled, pullCursor >>
     \/ /\ pullCursor # Null
        /\ LET
              filtered == {i \in log : i.created > pullCursor.lastId /\ i.modified <= pullCursor.startedAt}
              sorted == SetToSortSeq(filtered, SortByCreated)
              length == Len(sorted)
            IN
              \/ /\ length > 0
                 /\ pulled' = pulled \o SubSeq(sorted, 1, Min({pageSize, length}))
                 /\ pullCursor' = [pullCursor EXCEPT !.lastId = Last(pulled').created]
                 /\ UNCHANGED << pageSize, log, clock, synced, syncCursor >>
              \/ /\ length = 0
                 /\ syncCursor' = [lastId |-> pullCursor.lastId, lastModified |-> pullCursor.startedAt]
                 /\ UNCHANGED << pageSize, log, clock, synced, pulled, pullCursor >>
  
(* Ideal cursor update that cannot fail for now. *)
Sync ==
  /\ syncCursor # Null
  /\ LET
       filtered == {i \in log : 
                      \/ i.modified > syncCursor.lastModified 
                      \/ i.modified = syncCursor.lastModified /\ i.created  > syncCursor.lastId}
       sorted == SetToSortSeq(filtered, SortByModified)
       length == Len(sorted)
     IN
       /\ length > 0
       /\ synced' = synced \o SubSeq(sorted, 1, Min({pageSize, length}))
       /\ syncCursor' = [lastId |-> Last(synced').created, lastModified |-> Last(synced').modified]
       /\ UNCHANGED << pageSize, log, clock, pulled, pullCursor >>

  

\* (* Invariant. *)
\* ItemsPulledInCreatedOrder ==

\* (* Invariant. *)
\* ItemsSyncedInModifiedOrder ==

(* 
  Invariant. 

  Item.created can be treated as id.
  We're going to start by syncing every modification of Items.
  <<created, modified>> can be treated as id for modifications
*)
NoDuplicates ==
  /\ Cardinality({i.created : i \in Range(pulled)}) = Len(pulled)
  /\ Cardinality({<<i.created, i.modified>> : i \in Range(synced)}) = Len(synced)

(* Invariant.  *)
PulledInOrder ==
  /\ \A a, b \in DOMAIN pulled :
    (a # b /\ a > b) => pulled[a].created > pulled[b].created

(* Invariant.  *)
SyncedInOrder ==
  /\ \A a, b \in DOMAIN synced :
    (a # b /\ a > b) => synced[a].modified > synced[b].modified
    

(* *)
UpToDate ==
  /\ log \subseteq (Range(pulled) \union Range(synced))



(* 
  Allow infinite stuttering to prevent deadlock on termination. 
*)
Done ==
  /\ clock > MaxTimestamp
  /\ UpToDate
  /\ UNCHANGED vars

Next ==
  \/ Create
  \* \/ \E i \in 1..(clock - 1) :
  \*   \/ Modify(i)
  \/ Modify
  \/ Pull
  \/ Sync
  \/ Done

Spec ==
  /\ Init
  /\ [][Next]_vars

--------------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
--------------------------------------------------------------------------------

(*
  @todo Revisit simulation mode ? 
*)
FailOnDone ==
  ~(
    /\ ENABLED Done
    /\ TLCGet("level") > 3
  )

--------------------------------------------------------------------------------


================================================================================
LET
  s == << 2, 4, 1, 5 >>
IN
  SortSeq(
    s,
    LAMBDA a, b : a < b
  )

LET
  a == {3, 4, 5, 6}
  b == {4, 6}
IN
  a \subseteq b 