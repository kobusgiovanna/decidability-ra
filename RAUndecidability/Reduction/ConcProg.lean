import RAUndecidability.Reduction.Threads
import RAUndecidability.ProgramSemantics.LTS

/-!
# The concurrent program `ConcProg`

The twelve threads of `Reduction/Threads.lean`, each given its initial store
(the initial store (App. A): `cnt`/`cnt_y` ↦ `0`, each `fst` ↦ `True`, everything
else defaulted, since every program assigns its remaining locals before
reading them), wrapped through `inducedLTS`/`inducedSeqProgram`
(the induced LTS (App. A), sequential programs (§2.1)) and combined into one
`ConcurrentProgram` (§2.1).
-/

namespace RAUndecidability

variable (I : PCPInstance)

/-- The local state of each thread (`ConcurrentProgram.LocalState`): the
induced LTS's state set, at that thread's `Vocabulary`, `program`, and
concrete initial store. -/
def ConcLocalState : Tid → Type
  | .guessAX => InducedState (domainOf I) (GuessAX.Vocab I) .guessAX (GuessAX.program I)
      ((GuessAX.Vocab I).mkStore (fun v => match v with
        | .cntY => some (Sum.inr (Sum.inl (0 : Fin 4)))
        | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
        | .fst => some (Sum.inr (Sum.inr (Sum.inr true)))
        | _ => none) (Sum.inl none))
  | .guessAY => InducedState (domainOf I) (GuessAY.Vocab I) .guessAY (GuessAY.program I)
      ((GuessAY.Vocab I).mkStore (fun v => match v with
        | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
        | .fst => some (Sum.inr (Sum.inr true))
        | _ => none) (Sum.inl none))
  | .guessBX => InducedState (domainOf I) (GuessBX.Vocab I) .guessBX (GuessBX.program I)
      ((GuessBX.Vocab I).mkStore (fun v => match v with
        | .cntY => some (Sum.inr (Sum.inl (0 : Fin 4)))
        | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
        | .fst => some (Sum.inr (Sum.inr (Sum.inr true)))
        | _ => none) (Sum.inl none))
  | .guessBY => InducedState (domainOf I) (GuessBY.Vocab I) .guessBY (GuessBY.program I)
      ((GuessBY.Vocab I).mkStore (fun v => match v with
        | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
        | .fst => some (Sum.inr (Sum.inr true))
        | _ => none) (Sum.inl none))
  | .primeAX => InducedState (domainOf I) (PrimeAX.Vocab I) .primeAX (PrimeAX.program I)
      ((PrimeAX.Vocab I).mkStore (fun v => match v with
        | .cnt => some (Sum.inl (0 : Fin 4))
        | .b => none) (Sum.inl 0))
  | .primeAY => InducedState (domainOf I) (PrimeAY.Vocab I) .primeAY (PrimeAY.program I)
      ((PrimeAY.Vocab I).mkStore (fun v => match v with
        | .cnt => some (Sum.inl (0 : Fin 4))
        | .b => none) (Sum.inl 0))
  | .primeBX => InducedState (domainOf I) (PrimeBX.Vocab I) .primeBX (PrimeBX.program I)
      ((PrimeBX.Vocab I).mkStore (fun v => match v with
        | .cnt => some (Sum.inl (0 : Fin 4))
        | .b => none) (Sum.inl 0))
  | .primeBY => InducedState (domainOf I) (PrimeBY.Vocab I) .primeBY (PrimeBY.program I)
      ((PrimeBY.Vocab I).mkStore (fun v => match v with
        | .cnt => some (Sum.inl (0 : Fin 4))
        | .b => none) (Sum.inl 0))
  | .checkX => InducedState (domainOf I) (CheckX.Vocab I) .checkX (CheckX.program I)
      ((CheckX.Vocab I).mkStore (fun v => match v with
        | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
        | .fst => some (Sum.inr (Sum.inr true))
        | _ => none) (Sum.inl none))
  | .checkY => InducedState (domainOf I) (CheckY.Vocab I) .checkY (CheckY.program I)
      ((CheckY.Vocab I).mkStore (fun v => match v with
        | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
        | .fst => some (Sum.inr (Sum.inr true))
        | _ => none) (Sum.inl none))
  | .primeCheckX => InducedState (domainOf I) (PrimeCheckX.Vocab I) .primeCheckX
      (PrimeCheckX.program I)
      ((PrimeCheckX.Vocab I).mkStore (fun v => match v with
        | .cnt => some (Sum.inl (0 : Fin 4))
        | .b => none) (Sum.inl 0))
  | .primeCheckY => InducedState (domainOf I) (PrimeCheckY.Vocab I) .primeCheckY
      (PrimeCheckY.program I)
      ((PrimeCheckY.Vocab I).mkStore (fun v => match v with
        | .cnt => some (Sum.inl (0 : Fin 4))
        | .b => none) (Sum.inl 0))

/-- The sequential program of each thread (`ConcurrentProgram.prog`). -/
def ConcProgOf : (t : Tid) → SequentialProgram (domainOf I) t (ConcLocalState I t)
  | .guessAX => inducedSeqProgram
  | .guessAY => inducedSeqProgram
  | .guessBX => inducedSeqProgram
  | .guessBY => inducedSeqProgram
  | .primeAX => inducedSeqProgram
  | .primeAY => inducedSeqProgram
  | .primeBX => inducedSeqProgram
  | .primeBY => inducedSeqProgram
  | .checkX => inducedSeqProgram
  | .checkY => inducedSeqProgram
  | .primeCheckX => inducedSeqProgram
  | .primeCheckY => inducedSeqProgram

/-- **Paper:** Fig. 7.

The concurrent program `ConcProg` (Fig. 7) for a PCP instance
`I`. -/
def ConcProg : ConcurrentProgram (domainOf I) where
  LocalState := ConcLocalState I
  prog := ConcProgOf I

end RAUndecidability
