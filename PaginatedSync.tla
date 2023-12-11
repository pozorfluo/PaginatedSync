----------------------------- MODULE PaginatedSync -----------------------------
EXTENDS Naturals, FiniteSets, Functions

--------------------------------------------------------------------------------
set ++ e == set \union {e}
set -- e == set \ {e}
--------------------------------------------------------------------------------
CONSTANT
  MaxPageSize,
  MaxTimestamp

ASSUME
  /\ MaxPageSize \in Nat \ {0}
  /\ MaxTimestamp \in Nat
  /\ MaxTimestamp > 2


VARIABLES
  clock,
  pageSize,
  pulled,
  synced

vars ==
  << clock, log, pageSize, pulled, synced >>

--------------------------------------------------------------------------------
Timestamps ==
  1..MaxTimestamp

Items ==
  [created : Timestamps, modified : Timestamps]
  
--------------------------------------------------------------------------------
(* Invariant. *)
TypeInvariant ==
  /\ clock \in Nat
  /\ pageSize \in Nat
  /\ log \in SUBSET Items
  /\ pull \in Seq(Items)
  /\ synced \in Seq(Items)

Init ==
  /\ clock = (MaxTimestamp \div 2) + 1
  /\ pageSize \in 1..MaxPageSize
  /\ log = { [created |-> t, modified |-> t] : t \in 1..(MaxTimestamp \div 2) }
  /\ pull = <<>>
  /\ synced = <<>>



Create ==
  \* Exclude pointless Create before first pull.  
  /\ pull # <<>>
  /\ clock <= MaxTimestamp
  /\ log' = log ++ [created |-> clock, modified |-> clock]
  /\ clock' = clock + 1
  /\ UNCHANGED << pageSize, pulled, synced >>

Modify(id) ==
  \* Exclude pointless Modify before first pull.  
  /\ pull # <<>>
  /\ clock <= MaxTimestamp
  /\ log' = { IF i.created = id THEN [created |-> id, modified |-> clock] ELSE i : i \in log }
  /\ clock' = clock + 1
  /\ UNCHANGED << pageSize, pulled, synced >>
  
Pull() ==
  
Sync() 
  

(* Invariant. *)
ItemsPulledInCreatedOrder ==

(* Invariant. *)
ItemsSyncedInModifiedOrder ==

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
  \/ Done

Spec ==
  /\ Init
  /\ [][Next]_vars

================================================================================
