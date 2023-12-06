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


VARIABLES
  clock,
  pageSize,
  pulled,
  synced

vars ==
  << clock, pageSize, pulled, synced >>

--------------------------------------------------------------------------------
Timestamps ==
  1..MaxTimestamp

Items ==
  [created : Timestamps, modified : Timestamps]
  
--------------------------------------------------------------------------------
(* Invariant. *)
TypeInvariant ==
  /\ opCount \in Nat
  /\ pageSize \in Nat
  /\ pull \in Seq(Items)
  /\ synced \in Seq(Items)

Init ==
  /\ opCount = 0
  /\ pageSize \in 1..MaxPageSize



Create() ==

Modify() ==
  
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
(* Invariant. *)

(* 
  Allow infinite stuttering to prevent deadlock on termination. 
*)
Done ==
  /\ 
  /\ UNCHANGED vars

Next ==
  \/ 

Spec ==
  /\ Init
  /\ [][Next]_vars

================================================================================
