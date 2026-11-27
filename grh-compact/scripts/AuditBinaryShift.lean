import Conjectures.Goldbach.BinaryShiftExceptionUnion

/- The right-hand type is the frozen statement from the research lease.
No section variables, typeclass binders or zero-line assumptions are introduced. -/
example : let G := fun m : ℕ => ((Finset.range (m+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card; ∃ X₀ : ℕ, ∀ X ≥ X₀, let L := Nat.log 2 X / 2; let E := (Finset.Ico X (2*X)).filter (fun n => Even n ∧ 0 < ((Finset.Icc 1 L).filter (fun e => G (n-2^e)=0)).card); E.card^5 ≤ X^4 :=
  Conjectures.Goldbach.BinaryShiftExceptionUnion

#check Conjectures.Goldbach.BinaryShiftExceptionUnion
#print axioms LFunction_eq_zero_re
#print axioms Conjectures.Goldbach.BinaryShiftExceptionUnion
