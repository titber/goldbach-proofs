import Main
import PEqualNP.Outside.L_goldbach_grh_goldbach_exception_density
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Local reduction, not the unconditional registered theorem.
A power bound on the ordinary Goldbach exceptional set is the only input.
An eventual Pintz bound with exponent 18/25 implies the weaker 3/4 input. -/

namespace GoldbachBinaryShiftReduction
open Finset

def reps (m : ℕ) : ℕ :=
  ((range (m+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card

def exceptions (Y : ℕ) : Finset ℕ :=
  (Icc 4 Y).filter (fun m => Even m ∧ reps m = 0)

def badShift (X : ℕ) : Finset ℕ :=
  (Ico X (2*X)).filter (fun n => Even n ∧ 0 <
    ((Icc 1 (Nat.log 2 X / 2)).filter (fun e => reps (n-2^e) = 0)).card)

private theorem count_with_cover {X : ℕ} (hx : 8 ≤ X) (D : Finset ℕ)
    (cover : ∀ m ∈ exceptions (2*X), X/2 ≤ m → m ∈ D) :
    (badShift X).card ≤ D.card * (Nat.log 2 X / 2) := by
  let H := Icc 1 (Nat.log 2 X / 2)
  let addShift := fun u : ℕ × ℕ => u.1 + 2^u.2
  have sub : badShift X ⊆ (D ×ˢ H).image addShift := by
    intro n hn
    obtain ⟨hnI, hEven, hSome⟩ := mem_filter.mp hn
    obtain ⟨hlo,hhi⟩ := mem_Ico.mp hnI
    obtain ⟨e,he⟩ := card_pos.mp hSome
    obtain ⟨heH, hrep⟩ := mem_filter.mp he
    obtain ⟨he1,heL⟩ := mem_Icc.mp heH
    have hsq := Nat.pow_le_of_le_log (b:=2) (x:=e+e) (y:=X) (by omega) (by omega)
    rw [pow_add] at hsq
    have htwo : 2 ≤ 2^e := by
      exact (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) he1 : 2^1 ≤ 2^e)
    have hdouble : 2^e+2^e ≤ X := by
      have h := Nat.mul_le_mul_right (2^e) htwo
      rw [two_mul] at h
      exact h.trans hsq
    have hle : 2^e ≤ n := by omega
    have hpow : Even ((2:ℕ)^e) := even_two.pow_of_ne_zero (by omega)
    have hdiff : Even (n-2^e) := (Nat.even_sub hle).mpr ⟨fun _ => hpow, fun _ => hEven⟩
    have hm : n-2^e ∈ D := by
      apply cover _ _ (by omega)
      apply mem_filter.mpr
      exact ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hdiff, hrep⟩
    exact mem_image.mpr ⟨(n-2^e,e), mem_product.mpr ⟨hm,heH⟩, Nat.sub_add_cancel hle⟩
  calc
    _ ≤ ((D ×ˢ H).image addShift).card := card_le_card sub
    _ ≤ (D ×ˢ H).card := card_image_le
    _ = _ := by simp [H, Nat.card_Icc]

theorem count_le {X : ℕ} (hx : 8 ≤ X) :
    (badShift X).card ≤ (exceptions (2*X)).card * (Nat.log 2 X / 2) :=
  count_with_cover hx _ (fun _ hm _ => hm)

private theorem absorb (k : ℕ) (hk : 256 ≤ k) : k^20 * 2^15 ≤ 2^k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have h1 : 256^20 * (k+1)^20 ≤ 257^20 * k^20 := by
      simpa only [mul_pow] using Nat.pow_le_pow_left (show 256*(k+1) ≤ 257*k by omega) 20
    have h2 : 257^20 * k^20 ≤ (2*256^20)*k^20 :=
      Nat.mul_le_mul_right _ (by decide)
    have step : (k+1)^20 ≤ 2*k^20 := by
      apply Nat.le_of_mul_le_mul_left (c := 256^20) _ (by decide)
      calc
        _ ≤ _ := h1.trans h2
        _ = _ := by ac_rfl
    calc
      (k+1)^20 * 2^15 ≤ (2*k^20)*2^15 := Nat.mul_le_mul_right _ step
      _ = 2*(k^20 * 2^15) := by ac_rfl
      _ ≤ 2*(2^k) := Nat.mul_le_mul_left _ ih
      _ = 2^(k+1) := by rw [pow_succ, Nat.mul_comm]

private theorem finish_count {X B : ℕ} (hx : 2^256 ≤ X)
    (hB : B^4 ≤ (2*X)^3) (hcnt : (badShift X).card ≤ B*(Nat.log 2 X/2)) :
    (badShift X).card^5 ≤ X^4 := by
  have h8 : 8 ≤ X := le_trans (by decide : 8 ≤ (2:ℕ)^256) hx
  let L := Nat.log 2 X / 2
  have hk : 256 ≤ Nat.log 2 X := (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr hx
  have hL : L^20 * 2^15 ≤ X := calc
    _ ≤ (Nat.log 2 X)^20 * 2^15 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.div_le_self _ _) _)
    _ ≤ 2^(Nat.log 2 X) := absorb _ hk
    _ ≤ X := Nat.pow_log_le_self 2 (by omega)
  have h := Nat.pow_le_pow_left hcnt 20
  apply (Nat.pow_le_pow_iff_left (n:=4) (by decide)).mp
  calc
    ((badShift X).card^5)^4 = (badShift X).card^20 := by ring
    _ ≤ (B*L)^20 := h
    _ = (B^4)^5 * L^20 := by ring
    _ ≤ ((2*X)^3)^5 * L^20 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hB 5)
    _ = (L^20*2^15)*X^15 := by ring
    _ ≤ X*X^15 := Nat.mul_le_mul_right _ hL
    _ = (X^4)^4 := by ring

/-- The quantified conclusion is the desk's frozen target, conditional only on
an ordinary, unshifted exceptional-set estimate (in integer arithmetic). -/
theorem of_exception_bound
    (hp : ∃ T : ℕ, ∀ Y ≥ T, (exceptions Y).card^4 ≤ Y^3) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, (badShift X).card^5 ≤ X^4 := by
  obtain ⟨T,hT⟩ := hp
  refine ⟨max T (2^256), ?_⟩
  intro X hX
  have ht := (le_max_left T (2^256)).trans hX
  have hx := (le_max_right T (2^256)).trans hX
  have h8 : 8 ≤ X := le_trans (by decide : 8 ≤ (2:ℕ)^256) hx
  exact finish_count hx (hT _ (by omega)) (count_le h8)

/-- Adapter for an integer version of the published 18/25 estimate.
No analytic exception theorem is postulated or proved by this adapter. -/
theorem frozen_of_pintz
    (hp : ∃ T : ℕ, ∀ Y ≥ T, (exceptions Y).card^25 ≤ Y^18) :
    let G := fun m : ℕ => ((Finset.range (m+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card; ∃ X₀ : ℕ, ∀ X ≥ X₀, let L := Nat.log 2 X / 2; let E := (Finset.Ico X (2*X)).filter (fun n => Even n ∧ 0 < ((Finset.Icc 1 L).filter (fun e => G (n-2^e)=0)).card); E.card^5 ≤ X^4 := by
  apply of_exception_bound
  obtain ⟨T,hT⟩ := hp
  refine ⟨max T 1, ?_⟩
  intro Y hY
  have ht := (le_max_left T 1).trans hY
  have hy := (le_max_right T 1).trans hY
  apply (Nat.pow_le_pow_iff_left (n:=25) (by decide)).mp
  calc
    ((exceptions Y).card^4)^25 = ((exceptions Y).card^25)^4 := by ring
    _ ≤ (Y^18)^4 := Nat.pow_le_pow_left (hT Y ht) 4
    _ = Y^72 := by ring
    _ ≤ Y^75 := Nat.pow_le_pow_right (by omega) (by decide)
    _ = (Y^3)^25 := by ring

private def bad (m : ℕ) : Prop :=
  4 ≤ m ∧ Even m ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=m

private noncomputable def exc (I : Finset ℕ) : Finset ℕ :=
  @Finset.filter ℕ bad (Classical.decPred bad) I

private theorem bad_of_mem {m Y : ℕ} (hm : m ∈ exceptions Y) : bad m := by
  obtain ⟨hI,hev,hzero⟩ := mem_filter.mp hm
  refine ⟨(mem_Icc.mp hI).1, hev, ?_⟩
  rintro ⟨p,q,hp,hq,hpq⟩
  have hpos : 0 < reps m := card_pos.mpr ⟨p, mem_filter.mpr
    ⟨mem_range.mpr (by omega), hp, by simpa only [show m-p = q by omega]⟩⟩
  omega

private theorem absorb_real {C : ℝ} {Y B : ℕ} (hY : C^12 ≤ (Y:ℝ))
    (hb : (B:ℝ) ≤ C*(Y:ℝ)^((2:ℝ)/3)) : B^4 ≤ Y^3 := by
  have h := pow_le_pow_left₀ (Nat.cast_nonneg B : (0:ℝ) ≤ B) hb 12
  rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg Y) _ 12,
      show (2:ℝ)/3 * (12:ℕ) = (8:ℕ) by norm_num, Real.rpow_natCast] at h
  have h12 : (B:ℝ)^12 ≤ (Y:ℝ)^9 := calc
    _ ≤ _ := h
    _ ≤ (Y:ℝ)*(Y:ℝ)^8 := mul_le_mul_of_nonneg_right hY (by positivity)
    _ = _ := by ring
  apply (Nat.pow_le_pow_iff_left (n:=3) (by decide)).mp
  rw [← pow_mul, ← pow_mul]
  exact_mod_cast h12

/-- Takes exactly the cumulative 4/7 + ε target as an assumption. -/
theorem frozen_of_four_sevenths (hg : let bad := fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n; ∀ e : ℝ, 0 < e → ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ X : ℕ, N ≤ X → ((@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Icc 4 X)).card : ℝ) ≤ C * (X:ℝ) ^ (4/7 + e)) : let G := fun m : ℕ => ((Finset.range (m+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card; ∃ X₀ : ℕ, ∀ X ≥ X₀, let L := Nat.log 2 X / 2; let E := (Finset.Ico X (2*X)).filter (fun n => Even n ∧ 0 < ((Finset.Icc 1 L).filter (fun e => G (n-2^e)=0)).card); E.card^5 ≤ X^4 := by
  classical
  obtain ⟨C,N,hC,H⟩ := hg (2/21) (by norm_num)
  obtain ⟨K,hK⟩ := exists_nat_ge (C^12)
  apply of_exception_bound
  refine ⟨max N K, ?_⟩
  intro Y hY
  have hN := (le_max_left N K).trans hY
  have hK' := (le_max_right N K).trans hY
  have hi : exceptions Y ⊆ exc (Icc 4 Y) := fun m hm =>
    mem_filter.mpr ⟨(mem_filter.mp hm).1,bad_of_mem hm⟩
  apply absorb_real (hK.trans (Nat.cast_le.mpr hK'))
  have h := H Y hN
  norm_num only [show (4:ℝ)/7 + 2/21 = 2/3 by norm_num] at h
  exact (Nat.cast_le.mpr (card_le_card hi)).trans h

/-- Takes exactly CountingBridge's dyadic output. A shift of n∈[X,2X)
lies in one of two adjacent blocks, including when X is odd. -/
theorem frozen_of_dyadic_four_sevenths (hd : let bad := fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n; ∀ e : ℝ, 0 < e → ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ X : ℕ, N ≤ X → ((@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Icc X (2*X))).card : ℝ) ≤ C * (X:ℝ) ^ (4/7 + e)) : let G := fun m : ℕ => ((Finset.range (m+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card; ∃ X₀ : ℕ, ∀ X ≥ X₀, let L := Nat.log 2 X / 2; let E := (Finset.Ico X (2*X)).filter (fun n => Even n ∧ 0 < ((Finset.Icc 1 L).filter (fun e => G (n-2^e)=0)).card); E.card^5 ≤ X^4 := by
  classical
  obtain ⟨C,N,hC,H⟩ := hd (2/21) (by norm_num)
  obtain ⟨K,hK⟩ := exists_nat_ge ((C+C)^12)
  refine ⟨max (2^256) (max (2*N) K), ?_⟩
  intro X hX
  have hx := (le_max_left _ _).trans hX
  have hm := (le_max_right _ _).trans hX
  have hN := (le_max_left _ _).trans hm
  have hK' := (le_max_right _ _).trans hm
  have h8 : 8 ≤ X := le_trans (by decide : 8 ≤ (2:ℕ)^256) hx
  let F := fun t : ℕ => exc (Icc t (2*t))
  let D := F (X/2) ∪ F X
  have hc : (badShift X).card ≤ D.card*(Nat.log 2 X/2) := by
    apply count_with_cover h8 D
    intro m hmem hlo
    have hb := bad_of_mem hmem
    have hmhi := (mem_Icc.mp (mem_filter.mp hmem).1).2
    by_cases hh : m < X
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨hlo,by omega⟩,hb⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,hmhi⟩,hb⟩)
  have heach (t : ℕ) (ht : N ≤ t) (htX : t ≤ X) :
      ((F t).card:ℝ) ≤ C*(X:ℝ)^((2:ℝ)/3) := by
    have h := H t ht
    rw [show (4:ℝ)/7 + 2/21 = 2/3 by norm_num] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg t) (Nat.cast_le.mpr htX) (by norm_num)) hC.le)
  have hcard : (D.card:ℝ) ≤ (C+C)*(X:ℝ)^((2:ℝ)/3) := calc
    _ ≤ (((F (X/2)).card:ℝ) + ((F X).card:ℝ)) := by
      exact_mod_cast card_union_le (F (X/2)) (F X)
    _ ≤ _ := by
      rw [add_mul]
      exact add_le_add (heach _ (by omega) (by omega)) (heach _ (by omega) le_rfl)
  have hB := absorb_real (hK.trans (Nat.cast_le.mpr hK')) hcard
  exact finish_count hx (hB.trans (Nat.pow_le_pow_left (by omega) 3)) hc


/-- A fixed dyadic 17/24 estimate suffices. Sum dyadic blocks geometrically
before invoking the existing cumulative exception bound. -/
theorem frozen_of_dyadic_two_thirds
    (hd : let bad := fun n : ℕ => 4 ≤ n ∧ Even n ∧
              ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n
          ∃ (C : ℝ) (N : ℕ), ∀ X : ℕ, N ≤ X →
            ((@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Icc X (2*X))).card : ℝ)
              ≤ C * (X:ℝ) ^ ((17:ℝ)/24)) : let G := fun m : ℕ => ((Finset.range (m+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card; ∃ X₀ : ℕ, ∀ X ≥ X₀, let L := Nat.log 2 X / 2; let E := (Finset.Ico X (2*X)).filter (fun n => Even n ∧ 0 < ((Finset.Icc 1 L).filter (fun e => G (n-2^e)=0)).card); E.card^5 ≤ X^4 := by
  classical
  apply of_exception_bound
  obtain ⟨C,N,H⟩ := hd
  let a : ℝ := 17/24
  let r : ℝ := 2^a
  have ha : 0 < a := by norm_num [a]
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) ha
  have hr0 : 0 ≤ r := by linarith
  have scale (k : ℕ) : ((2^k : ℕ):ℝ)^a = r^k := by
    push_cast
    dsimp only [r]
    rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
        ← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2), mul_comm (k:ℝ) a]
  let A := fun k : ℕ => ((exceptions (2^k)).card : ℝ)
  let D := max (A N) (C/(r-1))
  have hA0 (k : ℕ) : 0 ≤ A k := Nat.cast_nonneg _
  have hD : 0 ≤ D := (hA0 N).trans (le_max_left ..)
  have hDr : C ≤ D*(r-1) := (div_le_iff₀ (sub_pos.mpr hr)).mp (le_max_right ..)
  have series (k : ℕ) (hk : N ≤ k) : A k ≤ D*r^k := by
    induction k,hk using Nat.le_induction with
    | base =>
      exact (le_max_left ..).trans
        (le_mul_of_one_le_right hD (one_le_pow₀ hr.le))
    | succ k hk ih =>
      let t := 2^k
      let F := exc (Icc t (2*t))
      have hsub : exceptions (2^(k+1)) ⊆ exceptions t ∪ F := by
        intro m hm
        have h := mem_filter.mp hm
        have hI := mem_Icc.mp h.1
        by_cases hmle : m ≤ t
        · exact mem_union_left _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨hI.1,hmle⟩,h.2⟩)
        · apply mem_union_right
          apply mem_filter.mpr
          exact ⟨mem_Icc.mpr ⟨by omega, by simpa [t,pow_succ,mul_comm] using hI.2⟩,bad_of_mem hm⟩
      have hcnt : A (k+1) ≤ A k + (F.card:ℝ) := by
        dsimp only [A]
        exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
      have ht : N ≤ t := hk.trans (Nat.le_of_lt (Nat.lt_two_pow_self))
      have hf : (F.card:ℝ) ≤ C*r^k := (H t ht).trans_eq (by rw [← scale])
      calc
        _ ≤ _ := hcnt
        _ ≤ D*r^k + C*r^k := add_le_add ih hf
        _ ≤ D*r^k + (D*(r-1))*r^k :=
          add_le_add_right (mul_le_mul_of_nonneg_right hDr (pow_nonneg hr0 k)) _
        _ = D*r^(k+1) := by rw [pow_succ]; ring
  obtain ⟨K,hK⟩ := exists_nat_ge ((D*r)^24)
  refine ⟨max (2^N) K, ?_⟩
  intro Y hY
  have hNY := (le_max_left _ _).trans hY
  have hKY := (le_max_right _ _).trans hY
  have hy : Y ≠ 0 := Nat.ne_of_gt ((pow_pos (by decide : 0 < (2:ℕ)) N).trans_le hNY)
  let k := Nat.log 2 Y
  have hk : N ≤ k := (Nat.le_log_iff_pow_le (by decide) hy).mpr hNY
  have hupper : Y ≤ 2^(k+1) := (Nat.lt_pow_succ_log_self (by decide) Y).le
  have hsub : exceptions Y ⊆ exceptions (2^(k+1)) := by
    intro m hm
    have h := mem_filter.mp hm
    have hi := mem_Icc.mp h.1
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hi.1,hi.2.trans hupper⟩,h.2⟩
  have h_rk : r^k ≤ (Y:ℝ)^a := by
    rw [← scale]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr (Nat.pow_log_le_self 2 hy)) ha.le
  have hb : ((exceptions Y).card:ℝ) ≤ D*r*(Y:ℝ)^a := calc
    _ ≤ A (k+1) := Nat.cast_le.mpr (card_le_card hsub)
    _ ≤ _ := series _ (by omega)
    _ = D*r*r^k := by rw [pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h_rk (mul_nonneg hD hr0)
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg _ : (0:ℝ) ≤ (exceptions Y).card) hb 24
  rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg Y) _ 24,
      show a * (24:ℕ) = (17:ℕ) by norm_num [a], Real.rpow_natCast] at hp
  have h24 : ((exceptions Y).card:ℝ)^24 ≤ (Y:ℝ)^18 := calc
    _ ≤ _ := hp
    _ ≤ (Y:ℝ)*(Y:ℝ)^17 := mul_le_mul_of_nonneg_right (hK.trans (Nat.cast_le.mpr hKY)) (by positivity)
    _ = _ := by ring
  apply (Nat.pow_le_pow_iff_left (n:=6) (by decide)).mp
  rw [← pow_mul, ← pow_mul]
  exact_mod_cast h24

end GoldbachBinaryShiftReduction

/- Research closure with the exact Dirichlet zero-line premise, kept distinct
from applying the GRH proof. The density theorem is the community module
PEqualNP.Outside.L_goldbach_grh_goldbach_exception_density. Choose ε=1/6:
C·Y^(2/3) gives |exceptions Y|^12 ≤ C^12 Y^8 ≤ Y^9 eventually. -/
namespace GoldbachBinaryShiftReduction
open Finset
open scoped Classical

theorem frozen_under_dirichlet_line (h : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    0<s.re → s.re<1 → χ.LFunction s=0 → s.re=1/2) :
    let G := fun m : ℕ => ((Finset.range (m+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card; ∃ X₀ : ℕ, ∀ X ≥ X₀, let L := Nat.log 2 X / 2; let E := (Finset.Ico X (2*X)).filter (fun n => Even n ∧ 0 < ((Finset.Icc 1 L).filter (fun e => G (n-2^e)=0)).card); E.card^5 ≤ X^4 := by
  apply of_exception_bound
  obtain ⟨C,X₀,hC,HH⟩ := PEqualNP.Outside.L_goldbach_grh_goldbach_exception_density h (1/6) (by norm_num)
  obtain ⟨K,hK⟩ := exists_nat_ge (C^12)
  refine ⟨max K X₀,fun X hX => ?_⟩
  have heq : exceptions X = (range (X+1)).filter (fun n => 4≤n ∧ n%2=0 ∧ reps n=0) := by
    ext n
    simp only [exceptions,mem_filter,mem_range,mem_Icc,Nat.even_iff]
    omega
  have hb := HH X ((le_max_right ..).trans hX)
  rw [heq]
  change (((range (X+1)).filter (fun n => 4≤n ∧ n%2=0 ∧ reps n=0)).card:ℝ) ≤ C*(X:ℝ)^(1/2+1/6:ℝ) at hb
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg _ : (0:ℝ)≤_) hb 12
  rw [mul_pow,←Real.rpow_mul_natCast (Nat.cast_nonneg X),show (1/2+1/6:ℝ)*(12:ℕ)=(8:ℕ) by norm_num,Real.rpow_natCast] at hp
  have hk : C^12 ≤ (X:ℝ) := hK.trans (Nat.cast_le.mpr ((le_max_left ..).trans hX))
  have hz := hp.trans (mul_le_mul_of_nonneg_right hk (show 0≤(X:ℝ)^8 by positivity))
  apply (Nat.pow_le_pow_iff_left (n:=3) (by decide)).mp
  rw [←pow_mul,←pow_mul]
  norm_num
  exact_mod_cast (show _ ≤ (X:ℝ)^9 from hz.trans_eq (by ring))

end GoldbachBinaryShiftReduction

#print axioms GoldbachBinaryShiftReduction.frozen_under_dirichlet_line

/-- The registered conclusion, with the repository's formal Dirichlet zero-line
theorem supplied as a proof (not as an axiom or an argument of this theorem). -/
theorem Conjectures.Goldbach.BinaryShiftExceptionUnion :
    let G := fun m : ℕ => ((Finset.range (m+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card; ∃ X₀ : ℕ, ∀ X ≥ X₀, let L := Nat.log 2 X / 2; let E := (Finset.Ico X (2*X)).filter (fun n => Even n ∧ 0 < ((Finset.Icc 1 L).filter (fun e => G (n-2^e)=0)).card); E.card^5 ≤ X^4 :=
  GoldbachBinaryShiftReduction.frozen_under_dirichlet_line LFunction_eq_zero_re

#print axioms LFunction_eq_zero_re
#print axioms Conjectures.Goldbach.BinaryShiftExceptionUnion