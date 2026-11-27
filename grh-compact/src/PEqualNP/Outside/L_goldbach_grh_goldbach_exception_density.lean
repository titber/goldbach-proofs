import Mathlib

/-! Dirichlet character estimates, major arcs, and the exceptional set in the binary Goldbach problem. -/

private theorem binaryShift_squarefree_prod_primeFactors (n : ℕ) :
    Squarefree (∏ p ∈ n.primeFactors, p) :=
  Finset.squarefree_prod_of_pairwise_isCoprime
    (fun _ hp _ hq hpq ↦ Nat.coprime_iff_isRelPrime.mp <|
      (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hq)).mpr hpq)
    fun _ hp ↦ (Nat.prime_of_mem_primeFactors hp).prime.squarefree

namespace GoldbachDensityProgression
open scoped BigOperators Classical
open ArithmeticFunction

/-- Removing all indices that are not coprime to the modulus loses at most
one logarithm of the cutoff per distinct prime divisor of the modulus. -/
theorem sum_vonMangoldt_not_coprime_le (q X : ℕ) (hq : 0 < q) (hX : 0 < X) :
    (∑ n ∈ (Finset.range (X + 1)).filter (fun n => ¬n.Coprime q), vonMangoldt n) ≤
      (q.primeFactors.card : ℝ) * Real.log (X : ℝ) := by
  classical
  let bad := (Finset.range (X + 1)).filter (fun n => ¬n.Coprime q)
  let powers := bad.filter IsPrimePow
  have hsupport : ∑ n ∈ powers, vonMangoldt n = ∑ n ∈ bad, vonMangoldt n := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hn'
    exact vonMangoldt_eq_zero_iff.mpr
      (fun hpow => hn' (Finset.mem_filter.mpr ⟨hn, hpow⟩))
  have hinfo {n : ℕ} (hn : n ∈ powers) :
      n ≤ X ∧ ¬n.Coprime q ∧ IsPrimePow n := by
    obtain ⟨hbad, hp⟩ := Finset.mem_filter.mp hn
    obtain ⟨hrange, hnc⟩ := Finset.mem_filter.mp hbad
    exact ⟨Nat.le_of_lt_succ (Finset.mem_range.mp hrange), hnc, hp⟩
  have hmaps : ∀ n ∈ powers, n.minFac ∈ q.primeFactors := by
    intro n hn
    obtain ⟨_, hnc, hpow⟩ := hinfo hn
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpow
    rw [hp.pow_minFac hk.ne']
    apply hp.mem_primeFactors _ hq.ne'
    by_contra hnd
    exact hnc ((Nat.coprime_pow_left_iff hk p q).2 (hp.coprime_iff_not_dvd.mpr hnd))
  have hfiber (p : ℕ) (hpq : p ∈ q.primeFactors) :
      (∑ n ∈ powers.filter (fun n => n.minFac = p), vonMangoldt n) ≤
        Real.log (X : ℝ) := by
    have hp : Nat.Prime p := Nat.prime_of_mem_primeFactors hpq
    have hsub : powers.filter (fun n => n.minFac = p) ⊆ (p ^ Nat.log p X).divisors := by
      intro n hn
      obtain ⟨hn', hmin⟩ := Finset.mem_filter.mp hn
      obtain ⟨hnX, _, hpow⟩ := hinfo hn'
      obtain ⟨k, _, _, heq⟩ := (isPrimePow_nat_iff_bounded_log_minFac n).mp hpow
      rw [hmin] at heq
      have hk : k ≤ Nat.log p X := (Nat.le_log_iff_pow_le hp.one_lt hX.ne').2
        (heq ▸ hnX)
      apply Nat.mem_divisors.mpr
      refine ⟨?_, pow_ne_zero _ hp.ne_zero⟩
      rw [heq]
      exact pow_dvd_pow p hk
    calc
      _ ≤ ∑ n ∈ (p ^ Nat.log p X).divisors, vonMangoldt n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => vonMangoldt_nonneg)
      _ = Real.log ((p ^ Nat.log p X : ℕ) : ℝ) := vonMangoldt_sum
      _ ≤ _ := Real.log_le_log (by exact_mod_cast pow_pos hp.pos (Nat.log p X))
        (by exact_mod_cast Nat.pow_log_le_self p hX.ne')
  calc
    _ = ∑ n ∈ powers, vonMangoldt n := hsupport.symm
    _ = ∑ p ∈ q.primeFactors, ∑ n ∈ powers.filter (fun n => n.minFac = p),
          vonMangoldt n := (Finset.sum_fiberwise_of_maps_to hmaps (fun n => vonMangoldt n)).symm
    _ ≤ ∑ _p ∈ q.primeFactors, Real.log (X : ℝ) := Finset.sum_le_sum hfiber
    _ = _ := by simp [nsmul_eq_mul]

/-- The total contribution of noncoprime terms is bounded by a product of
two logarithms, uniformly in the modulus and cutoff. -/
theorem sum_vonMangoldt_not_coprime_le_logs (q X : ℕ) (hq : 0 < q) (hX : 0 < X) :
    (∑ n ∈ (Finset.range (X + 1)).filter (fun n => ¬n.Coprime q), vonMangoldt n) ≤
      (Real.log (q : ℝ) / Real.log 2) * Real.log (X : ℝ) := by
  have hpow : (2 : ℕ) ^ q.primeFactors.card ≤ q := by
    calc
      _ = ∏ _p ∈ q.primeFactors, (2 : ℕ) := by simp
      _ ≤ ∏ p ∈ q.primeFactors, p :=
        Finset.prod_le_prod (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      _ ≤ q := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  have hreal : (2 : ℝ) ^ q.primeFactors.card ≤ (q : ℝ) := by exact_mod_cast hpow
  have hcard : (q.primeFactors.card : ℝ) ≤ Real.log (q : ℝ) / Real.log 2 := by
    apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
    simpa only [Real.log_pow] using Real.log_le_log (by positivity) hreal
  exact (sum_vonMangoldt_not_coprime_le q X hq hX).trans
    (mul_le_mul_of_nonneg_right hcard
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ X from hX))))

/-- Raising the level of a Dirichlet character changes its finite twisted
von Mangoldt sum by at most the logarithmic cost of the excluded prime powers. -/
theorem changeLevel_twisted_sum_sub_le {d q : ℕ} (hd : d ∣ q) (hq : 0 < q)
    (χ : DirichletCharacter ℂ d) (X : ℕ) (hX : 0 < X) :
    ‖(∑ n ∈ Finset.range (X + 1),
        (DirichletCharacter.changeLevel hd χ) (n : ZMod q) * (vonMangoldt n : ℂ)) -
      (∑ n ∈ Finset.range (X + 1), χ (n : ZMod d) * (vonMangoldt n : ℂ))‖ ≤
      (Real.log (q : ℝ) / Real.log 2) * Real.log (X : ℝ) := by
  classical
  let ψ := DirichletCharacter.changeLevel hd χ
  let δ (n : ℕ) := ψ (n : ZMod q) * (vonMangoldt n : ℂ) -
    χ (n : ZMod d) * (vonMangoldt n : ℂ)
  have hterm (n : ℕ) : ‖δ n‖ ≤ if ¬n.Coprime q then vonMangoldt n else 0 := by
    by_cases hn : n.Coprime q
    · have hi : IsCoprime (n : ℤ) (q : ℤ) := hn.cast
      have heq : ψ (n : ZMod q) = χ (n : ZMod d) := by
        simpa [ψ] using χ.changeLevel_eq_cast_of_dvd' hd hi
      simp [δ, heq, hn]
    · have hz : ψ (n : ZMod q) = 0 :=
        MulChar.map_nonunit ψ (fun hu => hn ((ZMod.isUnit_iff_coprime n q).mp hu))
      simp only [δ, hz, zero_mul, zero_sub, norm_neg, norm_mul,
        Complex.norm_of_nonneg (vonMangoldt_nonneg (n := n)), ite_eq_left hn]
      exact mul_le_of_le_one_left vonMangoldt_nonneg (χ.norm_le_one _)
  calc
    _ = ‖∑ n ∈ Finset.range (X + 1), δ n‖ := by rw [← Finset.sum_sub_distrib]
    _ ≤ ∑ n ∈ Finset.range (X + 1), ‖δ n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range (X + 1), (if ¬n.Coprime q then vonMangoldt n else 0) :=
      Finset.sum_le_sum fun n _ => hterm n
    _ = ∑ n ∈ (Finset.range (X + 1)).filter (fun n => ¬n.Coprime q), vonMangoldt n := by
      rw [Finset.sum_filter]
    _ ≤ _ := sum_vonMangoldt_not_coprime_le_logs q X hq hX



noncomputable def twistedError {q : ℕ} (X : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  (∑ k ∈ Finset.range (X + 1), χ (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℂ)) -
    (if χ = 1 then (X : ℂ) else 0)

/-- Character orthogonality transfers a common error bound to every reduced residue class
without increasing it. -/
theorem progression_error_of_character_error (q a X : ℕ) [NeZero q] (ha : Nat.Coprime a q)
    (B : ℝ) (hχ : ∀ χ : DirichletCharacter ℂ q, ‖twistedError X χ‖ ≤ B) :
    |(∑ k ∈ (Finset.range (X + 1)).filter (fun k => k % q = a % q),
          ArithmeticFunction.vonMangoldt k) - (X : ℝ) / (q.totient : ℝ)| ≤ B := by
  let R := Finset.range (X + 1)
  let S : ℝ := ∑ k ∈ R.filter (fun k => k % q = a % q),
    ArithmeticFunction.vonMangoldt k
  let ψ (χ : DirichletCharacter ℂ q) : ℂ :=
    ∑ k ∈ R, χ (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℂ)
  let M (χ : DirichletCharacter ℂ q) : ℂ := if χ = 1 then (X : ℂ) else 0
  let t := (a : ZMod q)⁻¹
  have ha' : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).2 ha
  have ht : IsUnit t := isUnit_of_dvd_one ⟨(a : ZMod q), (ZMod.inv_mul_of_unit _ ha').symm⟩
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr q.pos_of_neZero
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hres : S = ∑ k ∈ R, ArithmeticFunction.vonMangoldt.residueClass (a : ZMod q) k := by
    simp only [S, Finset.sum_filter, ArithmeticFunction.vonMangoldt.residueClass,
      Set.indicator_apply, Set.mem_ofPred_eq, ZMod.natCast_eq_natCast_iff']
  -- Sum the pointwise character orthogonality identity over k ≤ X.
  have hexpand : (S : ℂ) =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ t * ψ χ := by
    rw [hres, Complex.ofReal_sum]
    simp_rw [ArithmeticFunction.vonMangoldt.residueClass_apply ha']
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro χ _
    simp only [ψ, t, Finset.mul_sum, mul_assoc]
  -- Only the principal character contributes a main term.
  have hmain : (∑ χ : DirichletCharacter ℂ q, χ t * M χ) = (X : ℂ) := by
    simp [M, mul_ite, MulChar.one_apply ht]
  have herr : ((S - (X : ℝ) / q.totient : ℝ) : ℂ) =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ t * (ψ χ - M χ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_div]
    simp only [Complex.ofReal_natCast, hexpand, mul_sub, Finset.sum_sub_distrib, hmain,
      div_eq_mul_inv]
    ring
  -- Bound each weighted error and count the φ(q) characters.
  have hsum : ‖∑ χ : DirichletCharacter ℂ q, χ t * (ψ χ - M χ)‖ ≤ (q.totient : ℝ) * B := by
    calc
      _ ≤ ∑ _χ : DirichletCharacter ℂ q, B := by
        apply norm_sum_le_of_le
        intro χ _
        rw [norm_mul]
        calc
          _ ≤ 1 * ‖ψ χ - M χ‖ :=
            mul_le_mul_of_nonneg_right (χ.norm_le_one t) (norm_nonneg _)
          _ ≤ B := by
            by_cases h : χ = 1 <;> simpa [twistedError, ψ, R, M, h] using hχ χ
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  change |S - (X : ℝ) / q.totient| ≤ B
  calc
    _ = ‖((S - (X : ℝ) / q.totient : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ = (q.totient : ℝ)⁻¹ * ‖∑ χ : DirichletCharacter ℂ q, χ t * (ψ χ - M χ)‖ := by
      rw [herr, norm_mul, norm_inv]
      simp
    _ ≤ (q.totient : ℝ)⁻¹ * ((q.totient : ℝ) * B) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hφ.le)
    _ = B := by rw [← mul_assoc, inv_mul_cancel₀ hφ.ne', one_mul]


/-- A common bound for primitive characters, including the character of conductor one,
implies a common progression bound. Raising the level costs at most
`log(q) log(X) / log(2)`. -/
theorem progression_error_of_primitive_character_error (K : ℝ)
    (hprim : ∀ (d X : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d),
      χ.IsPrimitive → 2 ≤ X → ‖twistedError X χ‖ ≤
        K * Real.sqrt (X : ℝ) * (Real.log (2 * (d : ℝ) * X)) ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ q a X : ℕ, 0 < q → Nat.Coprime a q → 2 ≤ X →
      |(Finset.sum ((Finset.range (X + 1)).filter (fun k => k % q = a % q))
          (fun k => ArithmeticFunction.vonMangoldt k)) - (X : ℝ) / (Nat.totient q : ℝ)| ≤
        C * Real.sqrt (X : ℝ) * (Real.log (2 * (q : ℝ) * X)) ^ 2 := by
  let M := max K 0
  let D := (Real.log 2)⁻¹
  have hM : 0 ≤ M := le_max_right _ _
  have hD : 0 < D := inv_pos.mpr (Real.log_pos (by norm_num))
  refine ⟨M + D, add_pos_of_nonneg_of_pos hM hD, ?_⟩
  intro q a X hq ha hX
  let : NeZero q := ⟨hq.ne'⟩
  let L := Real.log (2 * (q : ℝ) * X)
  have hx1 : 1 ≤ (X : ℝ) := by exact_mod_cast (show 1 ≤ X by omega)
  have hq1 : 1 ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q from hq)
  have hxpos : 0 < (X : ℝ) := by linarith
  have hqpos : 0 < (q : ℝ) := by linarith
  have hroot : 1 ≤ Real.sqrt (X : ℝ) := by simpa using Real.sqrt_le_sqrt hx1
  have hlogq : Real.log (q : ℝ) ≤ L := by
    apply Real.log_le_log hqpos
    calc
      (q : ℝ) ≤ 2 * q * 1 := by linarith
      _ ≤ 2 * q * X := mul_le_mul_of_nonneg_left hx1 (by positivity)
  have hlogX : Real.log (X : ℝ) ≤ L := by
    apply Real.log_le_log hxpos
    calc
      (X : ℝ) = 1 * X := (one_mul _).symm
      _ ≤ 2 * q * X := mul_le_mul_of_nonneg_right (by linarith) hxpos.le
  have hL : 0 ≤ L := (Real.log_nonneg hq1).trans hlogq
  have hprod : Real.log (q : ℝ) * Real.log (X : ℝ) ≤ L ^ 2 := by
    simpa only [pow_two] using mul_le_mul hlogq hlogX (Real.log_nonneg hx1) hL
  have hcost : Real.log (q : ℝ) / Real.log 2 * Real.log (X : ℝ) ≤
      D * Real.sqrt X * L ^ 2 := by
    calc
      _ = D * (Real.log (q : ℝ) * Real.log (X : ℝ)) := by
        dsimp only [D]
        rw [div_eq_mul_inv]
        ring
      _ ≤ D * L ^ 2 := mul_le_mul_of_nonneg_left hprod hD.le
      _ = D * 1 * L ^ 2 := by rw [mul_one]
      _ ≤ D * Real.sqrt X * L ^ 2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hroot hD.le) (sq_nonneg _)
  apply progression_error_of_character_error q a X ha
  intro χ
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hdpos : 0 < χ.conductor := Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hdq : (χ.conductor : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hq χ.conductor_dvd_level
  have hd1 : 1 ≤ (χ.conductor : ℝ) := by exact_mod_cast (show 1 ≤ χ.conductor from hdpos)
  let Ld := Real.log (2 * (χ.conductor : ℝ) * X)
  have hLd0 : 0 ≤ Ld := by
    apply Real.log_nonneg
    exact one_le_mul_of_one_le_of_one_le (by linarith) hx1
  have hLd : Ld ≤ L := by
    apply Real.log_le_log (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdq (by norm_num)) hxpos.le
  have hLd2 : Ld ^ 2 ≤ L ^ 2 := by
    simpa only [pow_two] using mul_le_mul hLd hLd hLd0 hL
  have hprimitive : ‖twistedError X χ.primitiveCharacter‖ ≤ M * Real.sqrt X * L ^ 2 := by
    calc
      _ ≤ K * Real.sqrt X * Ld ^ 2 := hprim _ X χ.primitiveCharacter
        χ.primitiveCharacter_isPrimitive hX
      _ ≤ M * Real.sqrt X * Ld ^ 2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)) (sq_nonneg _)
      _ ≤ M * Real.sqrt X * L ^ 2 := mul_le_mul_of_nonneg_left hLd2
        (mul_nonneg hM (Real.sqrt_nonneg _))
  have hone : χ = 1 ↔ χ.primitiveCharacter = 1 := by
    simpa only [χ.changeLevel_primitiveCharacter] using
      (DirichletCharacter.changeLevel_eq_one_iff (χ := χ.primitiveCharacter) χ.conductor_dvd_level)
  have hcorr : ‖twistedError X χ - twistedError X χ.primitiveCharacter‖ ≤
      Real.log (q : ℝ) / Real.log 2 * Real.log (X : ℝ) := by
    have h := changeLevel_twisted_sum_sub_le χ.conductor_dvd_level hq χ.primitiveCharacter
      X (show 0 < X by omega)
    rw [χ.changeLevel_primitiveCharacter] at h
    have cancel (u v m : ℂ) : (u - m) - (v - m) = u - v := by abel
    by_cases hprincipal : χ.primitiveCharacter = 1
    · have hprincipal' := hone.mpr hprincipal
      simpa only [twistedError, ite_eq_left hprincipal, ite_eq_left hprincipal', cancel] using h
    · have hprincipal' := mt hone.mp hprincipal
      simpa only [twistedError, ite_eq_right hprincipal, ite_eq_right hprincipal', cancel] using h
  calc
    _ = ‖(twistedError X χ - twistedError X χ.primitiveCharacter) +
        twistedError X χ.primitiveCharacter‖ := by rw [sub_add_cancel]
    _ ≤ _ := norm_add_le _ _
    _ ≤ D * Real.sqrt X * L ^ 2 + M * Real.sqrt X * L ^ 2 := by
      exact add_le_add (hcorr.trans hcost) hprimitive
    _ = (M + D) * Real.sqrt X * L ^ 2 := by ring

section

open Set Filter Complex DirichletCharacter

private theorem finite_compact_zeros {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {b : ℂ} (hb : f b ≠ 0) {K : Set ℂ} (hK : IsCompact K) :
    {z ∈ K | f z = 0}.Finite := by
  have ha : AnalyticOnNhd ℂ f univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have hd := ha.preimage_zero_mem_codiscreteWithin hb
    (show b ∈ (univ : Set ℂ) from mem_univ b) isConnected_univ
  exact (hK.finite_sdiff_of_mem_codiscreteWithin
    (Filter.codiscreteWithin_mono (subset_univ K) hd)).subset fun z hz => ⟨hz.1, by simp [hz.2]⟩

theorem finite_character_zeros_on_compact {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {K : Set ℂ} (hK : IsCompact K) :
    {z ∈ K | z ≠ 1 ∧ LFunction χ z = 0}.Finite := by
  by_cases hχ : χ = 1
  · subst χ
    refine (finite_compact_zeros (differentiable_LFunctionTrivChar₁ q)
      (LFunctionTrivChar₁_apply_one_ne_zero q) hK).subset ?_
    intro z hz
    refine ⟨hz.1, ?_⟩
    rw [LFunctionTrivChar₁, Function.update_of_ne hz.2.1]
    exact mul_eq_zero_of_right _ hz.2.2
  · have h₂ : LFunction χ 2 ≠ 0 := LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)
    exact (finite_compact_zeros (differentiable_LFunction hχ) h₂ hK).subset
      fun _ hz => ⟨hz.1, hz.2.2⟩

theorem finite_character_zeros_in_window {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t R : ℝ) :
    {z : ℂ | 0 < z.re ∧ z.re < 1 ∧ |z.im - t| ≤ R ∧ LFunction χ z = 0}.Finite := by
  let K := (Icc (0 : ℝ) 1) ×ℂ (Icc (t - R) (t + R))
  have hk : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  apply (finite_character_zeros_on_compact χ hk).subset
  intro z hz
  obtain ⟨h₀, h₁, him, hL⟩ := hz
  obtain ⟨hl, hr⟩ := abs_le.mp him
  refine ⟨⟨⟨h₀.le, h₁.le⟩, ⟨by linarith, by linarith⟩⟩, ?_, hL⟩
  intro he
  simp [he] at h₁

theorem positive_multiplicity_of_character_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {z : ℂ} (hz : z ≠ 1) (hL : LFunction χ z = 0) :
    0 < analyticOrderNatAt (LFunction χ) z := by
  let U := ({1}ᶜ : Set ℂ)
  have ha : AnalyticOnNhd ℂ (LFunction χ) U :=
    (show DifferentiableOn ℂ (LFunction χ) U from
      fun w hw => (differentiableAt_LFunction χ w (.inl hw)).differentiableWithinAt).analyticOnNhd
        isOpen_compl_singleton
  have hc : IsConnected U := isConnected_compl_singleton_of_one_lt_rank (by simp) 1
  have h₂ : (2 : ℂ) ∈ U := by simp [U]
  have hn : LFunction χ 2 ≠ 0 := LFunction_ne_zero_of_one_le_re χ (.inr (by norm_num)) (by norm_num)
  have hf : analyticOrderAt (LFunction χ) z ≠ ⊤ :=
    (ha.exists_analyticOrderAt_ne_top_iff_forall hc).mp
      ⟨⟨2, h₂⟩, by rw [(ha 2 h₂).analyticOrderAt_eq_zero.mpr hn]; simp⟩ ⟨z, hz⟩
  exact ENat.toNat_pos ((ha z hz).analyticOrderAt_ne_zero.mpr hL) hf

end

/-- On the line of real part three, the tail of the Dirichlet series has norm at
most one half. The lower bound is uniform in both the character and its modulus. -/
theorem half_le_norm_LFunction_of_re_eq_three {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : s.re = 3) :
    (1 / 2 : ℝ) ≤ ‖χ.LFunction s‖ := by
  have hhalf : 1 < s.re := by rw [hs]; norm_num
  let f := LSeries.term (fun n : ℕ => χ (n : ZMod q)) s
  let u (k : ℕ) : ℝ := 1 / (2 * ((k : ℝ) + 1))
  have hf : Summable f := χ.LSeriesSummable_of_one_lt_re hhalf
  have hterm (k : ℕ) : ‖f (k + 2)‖ ≤ u k - u (k + 1) := by
    have hk : k + 2 ≠ 0 := by omega
    have hnorm : ‖f (k + 2)‖ =
        ‖χ ((k + 2 : ℕ) : ZMod q)‖ / (((k : ℝ) + 2) ^ 3) := by
      simp only [f, LSeries.norm_term_eq, ite_eq_right hk, hs]
      norm_cast
    rw [hnorm]
    calc
      _ ≤ 1 / (((k : ℝ) + 2) ^ 3) :=
        div_le_div_of_nonneg_right (χ.norm_le_one _) (by positivity)
      _ ≤ _ := by
        simp only [u, Nat.cast_add_one]
        have h1 : 0 < (k : ℝ) + 1 := by positivity
        have h2 : 0 < (k : ℝ) + 2 := by positivity
        rw [show (k : ℝ) + 1 + 1 = k + 2 by ring]
        field_simp
        nlinarith [sq_nonneg (k : ℝ)]
  have htail : ‖∑' k : ℕ, f (k + 2)‖ ≤ 1 / 2 := by
    have hshift := (summable_nat_add_iff (f := f) 2).mpr hf
    apply le_of_tendsto hshift.hasSum.tendsto_sum_nat.norm
    apply Filter.Eventually.of_forall
    intro n
    calc
      _ ≤ ∑ k ∈ Finset.range n, (u k - u (k + 1)) :=
        norm_sum_le_of_le _ (fun k _ => hterm k)
      _ = u 0 - u n := Finset.sum_range_sub' u n
      _ ≤ 1 / 2 := by
        have hn : 0 ≤ u n := by dsimp [u]; positivity
        simpa [u] using sub_le_self (u 0) hn
  have hfirst : (∑ k ∈ Finset.range 2, f k) = 1 := by
    simp [Finset.sum_range_succ, f]
  have hsplit : (1 : ℂ) + (∑' k : ℕ, f (k + 2)) = χ.LFunction s := by
    rw [χ.LFunction_eq_LSeries hhalf, ← hfirst]
    exact hf.sum_add_tsum_nat_add 2
  have htriangle := norm_sub_le (χ.LFunction s) (∑' k : ℕ, f (k + 2))
  rw [← hsplit, add_sub_cancel_right, norm_one, hsplit] at htriangle
  linarith

section

open Metric MeromorphicOn

/-- On the critical line, a unit-height window lies inside the radius 11/4 disk
about 3 + it. Jensen's inequality on a slightly larger disk counts its zeros
with multiplicity. -/
theorem window_multiplicity_le_of_circle_bound (f : ℂ → ℂ) (t M : ℝ) (Z : Finset ℂ)
    (hZ : ∀ z ∈ Z, z.re = 1 / 2 ∧ |z.im - t| ≤ 1)
    (hf : AnalyticOnNhd ℂ f (closedBall (⟨3, t⟩ : ℂ) (23 / 8)))
    (hcenter : f (⟨3, t⟩ : ℂ) ≠ 0) (hM : 1 ≤ M)
    (hbound : ∀ z ∈ sphere (⟨3, t⟩ : ℂ) (23 / 8), ‖f z‖ ≤ M) :
    (∑ z ∈ Z, (analyticOrderNatAt f z : ℤ) : ℤ) ≤
      Real.log (M / ‖f (⟨3, t⟩ : ℂ)‖) / Real.log (23 / 22) := by
  classical
  let c : ℂ := ⟨3, t⟩
  let r : ℝ := 11 / 4
  let R : ℝ := 23 / 8
  have hr : 0 < r := by norm_num [r]
  have hR : 0 < R := by norm_num [R]
  have hrR : r < R := by norm_num [r, R]
  have han : AnalyticOnNhd ℂ f (closedBall c r) := hf.mono (closedBall_subset_closedBall hrR.le)
  have hmem (z : ℂ) (hz : z ∈ Z) : z ∈ closedBall c r := by
    obtain ⟨hre, him⟩ := hZ z hz
    have hs := sq_le_sq' (abs_le.mp him).1 (abs_le.mp him).2
    rw [mem_closedBall, dist_eq_norm]
    have heq := Complex.sq_norm_sub_sq_re (z - c)
    simp only [Complex.sub_re, Complex.sub_im, c, hre] at heq
    dsimp [r]
    nlinarith
  let d := divisor f (closedBall c r)
  have hd (z : ℂ) (hz : z ∈ Z) : (analyticOrderNatAt f z : ℤ) = d z := by
    change _ = divisor f (closedBall c r) z
    rw [han.divisor_apply (hmem z hz)]
    unfold analyticOrderNatAt
    cases h : analyticOrderAt f z using ENat.recTopCoe <;> simp
  have hsupp := d.finiteSupport (isCompact_closedBall c r)
  let U := Z ∪ hsupp.toFinset
  have hu : Function.support d ⊆ (U : Set ℂ) := by
    intro z hz
    exact Finset.mem_union_right _ (hsupp.mem_toFinset.mpr hz)
  have hsum : (∑ z ∈ Z, (analyticOrderNatAt f z : ℤ)) ≤ ∑ᶠ z, d z := by
    rw [finsum_eq_sum_of_support_subset _ hu]
    calc
      _ = ∑ z ∈ Z, d z := Finset.sum_congr rfl hd
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun z _ _ => han.divisor_nonneg z)
  have hj := AnalyticOnNhd.sum_divisor_le (c := c) (r := r) (R := R) (M := M)
    (by simpa only [abs_of_pos hr] using hr) (by simpa only [abs_of_pos hr, abs_of_pos hR] using hrR)
    hM (by simpa only [abs_of_pos hR] using hf) hcenter
    (by simpa only [abs_of_pos hR] using hbound)
  have hratio : R / r = 23 / 22 := by norm_num [R,r]
  rw [abs_of_pos hr, hratio] at hj
  exact le_trans (by exact_mod_cast hsum) hj

end

section

open Finset Filter Set MeasureTheory Complex Asymptotics
open scoped BigOperators Topology

private theorem complete_character_sum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) :
    ∑ k ∈ range q, χ (k : ZMod q) = 0 := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
    rw [← Fin.sum_univ_eq_sum_range]
    convert χ.sum_eq_zero_of_ne_one hne using 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt i.isLt)

private theorem char_partial_norm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)‖ ≤ (q : ℝ) + 1 := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hr (m : ℕ) : ‖∑ k ∈ range m, χ (k : ZMod q)‖ ≤ (q : ℝ) := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      by_cases hm : m < q
      · calc
          _ ≤ ∑ k ∈ range m, ‖χ (k : ZMod q)‖ := norm_sum_le _ _
          _ ≤ ∑ _k ∈ range m, (1 : ℝ) := Finset.sum_le_sum fun k _ => χ.norm_le_one _
          _ ≤ (q : ℝ) := by simpa using (Nat.cast_le.mpr hm.le : (m : ℝ) ≤ q)
      · have hmq : m = q + (m - q) := by omega
        conv_lhs => rw [hmq, sum_range_add, complete_character_sum χ hne, zero_add]
        simpa only [Nat.cast_add, ZMod.natCast_self, zero_add] using ih (m - q) (by omega)
  have htotal : ∑ k ∈ range (n+1), χ (k : ZMod q) =
      χ 0 + ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q) := by
    rw [Nat.range_succ_eq_Icc_zero,
      ← Finset.insert_Icc_add_one_left_eq_Icc n.zero_le, Finset.sum_insert (by simp)]
    simp
  have hdiff : (∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)) =
      (∑ k ∈ range (n+1), χ (k : ZMod q)) - χ 0 := by rw [htotal]; abel
  rw [hdiff]
  exact (norm_sub_le ..).trans (add_le_add (hr _) (χ.norm_le_one _))

private noncomputable def charSum {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod q)

private theorem charSum_measurable {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Measurable (charSum χ) :=
  (measurable_of_countable (f := fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q))).comp
    Nat.measurable_floor

private noncomputable def charMellin {q : ℕ} (χ : DirichletCharacter ℂ q) :=
  (Ioi (1 : ℝ)).indicator (charSum χ)

private theorem charMellin_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) :
    mellin (charMellin χ) (-s) =
      ∫ t in Ioi (1 : ℝ), charSum χ t * (t : ℂ) ^ (-(s + 1)) := by
  have hf : (fun t : ℝ => (t : ℂ) ^ (-s - 1) • charMellin χ t) =
      (Set.Ioi (1 : ℝ)).indicator (fun t : ℝ => charSum χ t * (t : ℂ) ^ (-(s+1))) := by
    funext t
    by_cases ht : t ∈ Ioi (1 : ℝ) <;>
      simp [charMellin, Set.indicator, ht, smul_eq_mul, show -s-1 = -(s+1) by ring, mul_comm]
  rw [mellin, hf, setIntegral_indicator measurableSet_Ioi,
    Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))]

theorem nonprincipal_LFunction_eq_partial_integral {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (s : ℂ) (hs : 0 < s.re) :
    χ.LFunction s = s * ∫ t in Ioi (1 : ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(s + 1)) := by
  let F := charMellin χ
  have hbound (t : ℝ) : ‖F t‖ ≤ (q : ℝ) + 1 := by
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · simpa [F, charMellin, Set.indicator_of_mem ht, charSum] using char_partial_norm χ hne ⌊t⌋₊
    · simp [F, charMellin, Set.indicator_of_notMem ht]
      positivity
  have hmeas : Measurable F := (charSum_measurable χ).indicator measurableSet_Ioi
  have hloc : LocallyIntegrableOn F (Ioi 0) := by
    apply (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).2
    intro K _ hK
    exact Measure.integrableOn_of_bounded hK.measure_lt_top.ne hmeas.aestronglyMeasurable
      (Eventually.of_forall hbound)
  have htop : F =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
    apply Asymptotics.IsBigO.of_bound ((q : ℝ) + 1)
    exact Eventually.of_forall (fun t => by simpa using hbound t)
  have hbot (b : ℝ) : F =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
    apply Asymptotics.IsBigO.of_bound 0
    have hsm : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [hsm] with t ht
    simp [F, charMellin, not_lt.mpr ht.le]
  let U := {z : ℂ | 0 < z.re}
  have ho : IsOpen U := continuous_re.isOpen_preimage (Set.Ioi (0:ℝ)) isOpen_Ioi
  have hd : AnalyticOnNhd ℂ (fun z : ℂ => z * mellin F (-z)) U := by
    apply DifferentiableOn.analyticOnNhd _ ho
    intro z hz
    have hm := mellin_differentiableAt_of_isBigO_rpow (s := -z) hloc htop
      (show (-z).re < 0 by simpa using (show 0 < z.re from hz)) (hbot ((-z).re - 1)) (by linarith)
    exact (differentiableAt_id.mul (hm.comp z differentiableAt_id.neg)).differentiableWithinAt
  have hχ : AnalyticOnNhd ℂ χ.LFunction U := by
    exact (χ.differentiable_LFunction hne).differentiableOn.analyticOnNhd ho
  have hagree : χ.LFunction =ᶠ[𝓝 (2:ℂ)] fun z => z * mellin F (-z) := by
    filter_upwards [(continuous_re.isOpen_preimage (Set.Ioi (1:ℝ)) isOpen_Ioi).mem_nhds
      (show 1 < (2:ℂ).re by norm_num)] with z hz
    have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q))
        =O[atTop] (fun n : ℕ => (n : ℝ) ^ (0 : ℝ)) := by
      apply Asymptotics.IsBigO.of_bound ((q : ℝ) + 1)
      exact Eventually.of_forall (fun n => by simpa using char_partial_norm χ hne n)
    rw [show F = charMellin χ from rfl, charMellin_eq, χ.LFunction_eq_LSeries hz]
    exact LSeries_eq_mul_integral _ le_rfl (zero_lt_one.trans hz) (χ.LSeriesSummable_of_one_lt_re hz) hO
  have hh := hχ.eqOn_of_preconnected_of_eventuallyEq hd (convex_halfSpace_re_gt 0).isPreconnected
    (show (2:ℂ) ∈ U by change 0 < (2:ℂ).re; norm_num) hagree hs
  simpa only [F, charMellin_eq, charSum] using hh

/-- The elementary vertical-growth bound from the bounded sums of a
nonprincipal character, throughout the open right half-plane. -/
theorem nonprincipal_LFunction_norm_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (s : ℂ) (hs : 0 < s.re) :
    ‖χ.LFunction s‖ ≤ ‖s‖ * ((q : ℝ) + 1) / s.re := by
  rw [nonprincipal_LFunction_eq_partial_integral χ hne s hs, norm_mul, mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have he : -(s.re + 1) < -1 := by linarith
  calc
    _ ≤ ∫ t in Set.Ioi (1 : ℝ), ((q : ℝ) + 1) * t ^ (-(s.re + 1)) := by
      apply norm_integral_le_of_norm_le
        ((integrableOn_Ioi_rpow_of_lt he zero_lt_one).const_mul ((q : ℝ) + 1))
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
      have ht' : (0 : ℝ) < t := zero_lt_one.trans ht
      simp only [norm_mul, norm_cpow_eq_rpow_re_of_pos ht', neg_re, add_re, one_re]
      exact mul_le_mul_of_nonneg_right (char_partial_norm χ hne _) (Real.rpow_nonneg ht'.le _)
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt he zero_lt_one,
        Real.one_rpow, show -(s.re + 1) + 1 = -s.re by ring]
      simp [div_eq_mul_inv]

/-- A uniform upper bound on the strip used to count zeros by Jensen's formula. -/
theorem nonprincipal_LFunction_norm_le_on_strip {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (s : ℂ) (hs : 1 / 8 ≤ s.re) :
    ‖χ.LFunction s‖ ≤ 16 * (q : ℝ) * ‖s‖ := by
  have hs' : 0 < s.re := by linarith
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  apply (nonprincipal_LFunction_norm_le χ hne s hs').trans
  apply (div_le_iff₀ hs').2
  have h1 := mul_le_mul_of_nonneg_right hs (show 0 ≤ 16 * (q : ℝ) * ‖s‖ by positivity)
  have h2 := mul_le_mul_of_nonneg_left hq (norm_nonneg s)
  linarith only [h1, h2]

end

section

open scoped BigOperators
open Metric

/-- Count nontrivial zeros of a nonprincipal character in a unit window
with their analytic multiplicities, uniformly in the modulus and height. -/
theorem nonprincipal_character_window_count {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ) (Z : Finset ℂ)
    (hGRH : ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 → z.re = 1 / 2)
    (hZ : ∀ z ∈ Z, 0 < z.re ∧ z.re < 1 ∧ χ.LFunction z = 0 ∧ |z.im - t| ≤ 1) :
    (∑ z ∈ Z, (analyticOrderNatAt χ.LFunction z : ℝ)) ≤
      (8 / Real.log (23 / 22)) * Real.log ((q : ℝ) * (2 + |t|)) := by
  let c : ℂ := ⟨3, t⟩
  let U : ℝ := (q : ℝ) * (2 + |t|)
  let M := 64 * U
  have hq : 1 ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q from q.pos_of_neZero)
  have hU : 2 ≤ U := calc
    (2 : ℝ) ≤ 2 + |t| := le_add_of_nonneg_right (abs_nonneg _)
    _ ≤ U := le_mul_of_one_le_left (by positivity) hq
  have hUpos : 0 < U := by linarith
  have hM : 1 ≤ M := by dsimp only [M]; linarith
  have hc : ‖c‖ ≤ 3 + |t| := by
    simpa [c] using Complex.norm_le_abs_re_add_abs_im c
  have hbound (z : ℂ) (hz : z ∈ sphere c (23 / 8)) : ‖χ.LFunction z‖ ≤ M := by
    have hdist : ‖z - c‖ = 23 / 8 := by simpa only [mem_sphere, dist_eq_norm] using hz
    have hre : |z.re - 3| ≤ 23 / 8 := by
      simpa only [Complex.sub_re, hdist, c] using Complex.abs_re_le_norm (z - c)
    have hl := (abs_le.mp hre).1
    have hzNorm : ‖z‖ ≤ 23 / 8 + (3 + |t|) := by
      calc ‖z‖ ≤ ‖z - c‖ + ‖c‖ := norm_le_norm_sub_add _ _
           _ ≤ _ := by rw [hdist]; linarith
    calc
      _ ≤ 16 * (q : ℝ) * ‖z‖ := nonprincipal_LFunction_norm_le_on_strip χ hχ z (by linarith)
      _ ≤ 16 * (q : ℝ) * (4 * (2 + |t|)) :=
        mul_le_mul_of_nonneg_left (by linarith [abs_nonneg t]) (by positivity)
      _ = M := by dsimp only [M, U]; ring
  have hlower : 1 / 2 ≤ ‖χ.LFunction c‖ := half_le_norm_LFunction_of_re_eq_three χ rfl
  have hcenter : 0 < ‖χ.LFunction c‖ := by linarith
  have hj := window_multiplicity_le_of_circle_bound χ.LFunction t M Z
    (fun z hz => ⟨hGRH z (hZ z hz).1 (hZ z hz).2.1 (hZ z hz).2.2.1, (hZ z hz).2.2.2⟩)
    (fun z _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z)
    (norm_pos_iff.mp hcenter) hM hbound
  have hratio : M / ‖χ.LFunction c‖ ≤ 128 * U := by
    apply (div_le_iff₀ hcenter).2
    calc
      M = 128 * U * (1 / 2) := by dsimp only [M]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlower (by positivity)
  have hlog : Real.log (M / ‖χ.LFunction c‖) ≤ 8 * Real.log U := by
    calc
      _ ≤ Real.log (128 * U) := Real.log_le_log (div_pos (by linarith) hcenter) hratio
      _ = 7 * Real.log 2 + Real.log U := by
        rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_mul (by norm_num) hUpos.ne', Real.log_pow]
        norm_num
      _ ≤ _ := by linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hU]
  have hden : 0 < Real.log (23 / 22) := Real.log_pos (by norm_num)
  calc
    _ ≤ Real.log (M / ‖χ.LFunction c‖) / Real.log (23 / 22) := by exact_mod_cast hj
    _ ≤ (8 * Real.log U) / Real.log (23 / 22) := div_le_div_of_nonneg_right hlog hden.le
    _ = _ := by dsimp only [U]; ring


end

section

open Set Complex MeasureTheory

noncomputable def perronWeight (t : ℝ) : ℂ :=
  (Ioc (0 : ℝ) 1).indicator (fun x => 1 - (x : ℂ)) t

theorem perronWeight_hasMellin {s : ℂ} (hs : 0 < s.re) :
    HasMellin perronWeight s (1 / (s * (s + 1))) := by
  have h₁ := hasMellin_one_Ioc hs
  have h₂ := hasMellin_cpow_Ioc 1 (s := s) (by simp; linarith)
  have h := hasMellin_sub h₁.1 h₂.1
  rw [h₁.2, h₂.2] at h
  have hfun : (fun t : ℝ => (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t -
      (Ioc (0 : ℝ) 1).indicator (fun u => (u : ℂ) ^ (1 : ℂ)) t) = perronWeight := by
    funext t
    by_cases ht : t ∈ Ioc (0 : ℝ) 1 <;> simp [perronWeight, ht]
  rw [hfun] at h
  convert h using 1
  have hz : s ≠ 0 := by intro h; simp [h] at hs
  have ho : s + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  field_simp
  ring

/-- The inverse Mellin transform on the line of real part two gives the usual
linear smoothing of a sharp cutoff. -/
theorem perronWeight_inversion {x : ℝ} (hx : 0 < x) :
    mellinInv 2 (fun s : ℂ => 1 / (s * (s + 1))) x = perronWeight x := by
  let s (t : ℝ) : ℂ := 2 + (t : ℂ) * I
  have hline (t : ℝ) : (s t).re = 2 := by simp [s]
  have htransform (t : ℝ) : mellin perronWeight (s t) = 1 / (s t * (s t + 1)) :=
    (perronWeight_hasMellin (by rw [hline]; norm_num)).2
  have hb (t : ℝ) : 1 + t ^ 2 ≤ ‖s t‖ * ‖s t + 1‖ := by
    have h1 := Complex.sq_norm (s t)
    have h2 := Complex.sq_norm (s t + 1)
    simp [s, Complex.normSq_apply] at h1 h2
    have hn : ‖s t‖ ≤ ‖s t + 1‖ := by nlinarith [norm_nonneg (s t + 1)]
    nlinarith [mul_le_mul_of_nonneg_left hn (norm_nonneg (s t))]
  have hv : VerticalIntegrable (mellin perronWeight) 2 := by
    change Integrable fun y : ℝ => mellin perronWeight (s y)
    simp_rw [htransform]
    apply integrable_inv_one_add_sq.mono'
    · exact (by fun_prop : Measurable (fun y : ℝ => 1 / (s y * (s y + 1)))).aestronglyMeasurable
    · apply Filter.Eventually.of_forall
      intro t
      rw [norm_div, norm_one, norm_mul, one_div]
      exact inv_anti₀ (by positivity) (hb t)
  have hcont : ContinuousAt perronWeight x := by
    have heq : perronWeight =ᶠ[nhds x] fun u : ℝ => ((max (1-u) 0 : ℝ) : ℂ) := by
      filter_upwards [lt_mem_nhds hx] with y hy
      by_cases h : y ≤ 1
      · simp [perronWeight, hy, h]
      · simp [perronWeight, h, max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]
    exact (by fun_prop : ContinuousAt (fun u : ℝ => ((max (1-u) 0 : ℝ) : ℂ)) x).congr_of_eventuallyEq heq
  have hi := mellinInv_mellin_eq 2 perronWeight hx (perronWeight_hasMellin (by norm_num)).1 hv hcont
  unfold mellinInv at hi ⊢
  simpa only [show ∀ t : ℝ, mellin perronWeight ((2 : ℝ) + (t : ℂ) * I) =
      1 / (((2 : ℝ) + (t : ℂ) * I) * (((2 : ℝ) + (t : ℂ) * I) + 1)) from htransform] using hi

end


section

open Finset Filter Set MeasureTheory Complex Asymptotics
open scoped BigOperators Topology

private noncomputable def fracPart (t : ℝ) : ℂ := ((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ)

private theorem measurable_fracPart : Measurable fracPart := by
  unfold fracPart
  fun_prop

private theorem frac_norm {t : ℝ} (ht : 0 ≤ t) : ‖fracPart t‖ ≤ 1 := by
  rw [fracPart, Complex.norm_of_nonneg (Nat.zero_le_self_sub_floor ht)]
  exact (Nat.self_sub_floor_lt_one t).le

private noncomputable def fracMellinFun := (Set.Ioi (1 : ℝ)).indicator fracPart

private theorem mellin_frac_eq (s : ℂ) :
    mellin fracMellinFun (-s) = ∫ t in Set.Ioi (1 : ℝ), fracPart t * (t : ℂ) ^ (-(s + 1)) := by
  have hf : (fun t : ℝ => (t : ℂ) ^ (-s - 1) • fracMellinFun t) =
      (Set.Ioi (1 : ℝ)).indicator (fun t : ℝ => fracPart t * (t : ℂ) ^ (-(s+1))) := by
    funext t
    by_cases ht : t ∈ Set.Ioi (1 : ℝ) <;>
      simp [fracMellinFun, Set.indicator, ht, smul_eq_mul, show -s-1 = -(s+1) by ring, mul_comm]
  rw [mellin, hf, setIntegral_indicator measurableSet_Ioi,
    Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))]

private theorem frac_kernel_bound (s : ℂ) {t : ℝ} (ht : 1 < t) :
    ‖fracPart t * (t : ℂ) ^ (-(s+1))‖ ≤ t ^ (-(s.re+1)) := by
  have ht' := zero_lt_one.trans ht
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht', neg_re, add_re, one_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg ht'.le _) (frac_norm ht'.le)

private theorem frac_kernel_integrable (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => fracPart t * (t : ℂ) ^ (-(s+1))) (Set.Ioi 1) := by
  apply (integrableOn_Ioi_rpow_of_lt (show -(s.re+1) < -1 by linarith) zero_lt_one).mono'
  · exact (measurable_fracPart.mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    exact frac_kernel_bound s ht

private theorem zeta_mellin_right (s : ℂ) (hs : 1 < s.re) :
    riemannZeta₁ s = s - (s - 1) * s * mellin fracMellinFun (-s) := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have h0 : 0 < s.re := zero_lt_one.trans hs
  have hZ : riemannZeta s =
      s * ∫ t in Set.Ioi (1 : ℝ), (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s+1)) := by
    rw [← LSeries_one_eq_riemannZeta hs, LSeries_eq_mul_integral (1 : ℕ → ℂ) zero_le_one
      hs (LSeriesSummable_one_iff.mpr hs)]
    · simp [Nat.card_Icc]
    · apply Asymptotics.IsBigO.of_bound 1
      exact Eventually.of_forall (fun n => by simp [Nat.card_Icc])
  have he : (-s).re < -1 := by simpa using hs
  have hI := integral_Ioi_cpow_of_lt he zero_lt_one
  have hc : (s - 1) * (∫ t : ℝ in Set.Ioi 1, (t : ℂ) ^ (-s)) = 1 := by
    rw [hI, ofReal_one, one_cpow, show -s + 1 = -(s - 1) by ring, neg_div_neg_eq]
    field_simp [sub_ne_zero.mpr hs1]
  have hsplit : (∫ t in Set.Ioi (1:ℝ), (⌊t⌋₊ : ℂ) * (t:ℂ)^(-(s+1))) =
      (∫ t : ℝ in Set.Ioi 1, (t:ℂ)^(-s)) - mellin fracMellinFun (-s) := by
    rw [mellin_frac_eq, ← integral_sub (integrableOn_Ioi_cpow_of_lt he zero_lt_one)
      (frac_kernel_integrable s h0)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have hz : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'
    have hp : (t:ℂ) ^ (-s) = (t:ℂ) * (t:ℂ) ^ (-(s+1)) := by
      conv_lhs => rw [show -s = 1 + (-(s+1)) by ring, cpow_add _ _ hz, cpow_one]
    dsimp only
    rw [hp, fracPart, ofReal_sub, ofReal_natCast]
    ring
  have hreg : riemannZeta₁ s = (s-1) * riemannZeta s := by
    rw [riemannZeta_eq_inv_sub_mul hs1, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs1), one_mul]
  rw [hreg, hZ, hsplit]
  linear_combination s * hc

/-- Euler's integral representation of the zeta function after removal of its
simple pole. The entire function on the left takes the value one at one. -/
theorem zeta_pole_removed_eq_floor_integral (s : ℂ) (hs : 0 < s.re) :
    riemannZeta₁ s = s - (s - 1) * s * ∫ t in Set.Ioi (1 : ℝ),
      (((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
  have hbound (t : ℝ) : ‖fracMellinFun t‖ ≤ 1 := by
    by_cases ht : t ∈ Set.Ioi (1 : ℝ)
    · simpa only [fracMellinFun, Set.indicator_of_mem ht] using frac_norm (zero_lt_one.trans ht).le
    · simp [fracMellinFun, Set.indicator_of_notMem ht]
  have hloc : LocallyIntegrableOn fracMellinFun (Set.Ioi 0) := by
    apply (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).2
    intro K _ hK
    exact Measure.integrableOn_of_bounded hK.measure_lt_top.ne
      (measurable_fracPart.indicator measurableSet_Ioi).aestronglyMeasurable
      (Eventually.of_forall hbound)
  have htop : fracMellinFun =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
    apply Asymptotics.IsBigO.of_bound 1
    exact Eventually.of_forall (fun t => by simpa using hbound t)
  have hbot (b : ℝ) : fracMellinFun =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
    apply Asymptotics.IsBigO.of_bound 0
    have hsm : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [hsm] with t ht
    simp [fracMellinFun, not_lt.mpr ht.le]
  let U := {z : ℂ | 0 < z.re}
  have ho : IsOpen U := continuous_re.isOpen_preimage (Set.Ioi (0:ℝ)) isOpen_Ioi
  have hd : AnalyticOnNhd ℂ (fun z : ℂ => z - (z - 1) * z * mellin fracMellinFun (-z)) U := by
    apply DifferentiableOn.analyticOnNhd _ ho
    intro z hz
    have hm := mellin_differentiableAt_of_isBigO_rpow (s := -z) hloc htop
      (show (-z).re < 0 by simpa using (show 0 < z.re from hz)) (hbot ((-z).re - 1)) (by linarith)
    exact (differentiableAt_id.sub (((differentiableAt_id.sub_const 1).mul differentiableAt_id).mul
      (hm.comp z differentiableAt_id.neg))).differentiableWithinAt
  have hZ := differentiable_riemannZeta₁.differentiableOn.analyticOnNhd ho
  have hagree : riemannZeta₁ =ᶠ[𝓝 (2:ℂ)] fun z => z - (z-1)*z*mellin fracMellinFun (-z) := by
    filter_upwards [(continuous_re.isOpen_preimage (Set.Ioi (1:ℝ)) isOpen_Ioi).mem_nhds
      (show 1 < (2:ℂ).re by norm_num)] with z hz
    exact zeta_mellin_right z hz
  have hh := hZ.eqOn_of_preconnected_of_eventuallyEq hd (convex_halfSpace_re_gt 0).isPreconnected
    (show (2:ℂ) ∈ U by change 0 < (2:ℂ).re; norm_num) hagree hs
  simpa only [mellin_frac_eq, fracPart] using hh

/-- Uniform polynomial growth of the entire pole-removed zeta function on
the half-plane containing the nonprincipal character strip. -/
theorem zeta_pole_removed_norm_le_on_strip (s : ℂ) (hs : 1 / 8 ≤ s.re) :
    ‖riemannZeta₁ s‖ ≤ 9 * (1 + ‖s‖)^2 := by
  have hs' : 0 < s.re := by linarith
  have he : -(s.re+1) < -1 := by linarith
  have hI : ‖∫ t in Set.Ioi (1:ℝ), fracPart t * (t:ℂ)^(-(s+1))‖ ≤ 8 := by
    calc
      _ ≤ ∫ t in Set.Ioi (1:ℝ), t ^ (-(s.re+1)) := by
        apply norm_integral_le_of_norm_le (integrableOn_Ioi_rpow_of_lt he zero_lt_one)
        filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
        exact frac_kernel_bound s ht
      _ ≤ 8 := by
        rw [integral_Ioi_rpow_of_lt he zero_lt_one, Real.one_rpow,
          show -(s.re+1)+1 = -s.re by ring, neg_div_neg_eq, div_le_iff₀ hs']
        linarith
  rw [zeta_pole_removed_eq_floor_integral s hs']
  apply (norm_sub_le ..).trans
  rw [norm_mul, norm_mul]
  have hsub : ‖s - 1‖ ≤ ‖s‖ + 1 := by simpa using norm_sub_le s (1:ℂ)
  calc
    _ ≤ ‖s‖ + (‖s‖ + 1) * ‖s‖ * 8 := by
      gcongr
      exact hI
    _ ≤ _ := by nlinarith [sq_nonneg ‖s‖, norm_nonneg s]

end

section

open scoped BigOperators Topology
open Metric

private theorem regular_zeta_eq_mul {z : ℂ} (hz : z ≠ 1) :
    riemannZeta₁ z = (z - 1) * riemannZeta z := by
  rw [riemannZeta_eq_inv_sub_mul hz, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hz), one_mul]

private theorem regular_zeta_order {z : ℂ} (hz : z ≠ 1) :
    analyticOrderNatAt riemannZeta₁ z = analyticOrderNatAt riemannZeta z := by
  have he : riemannZeta₁ =ᶠ[𝓝 z] fun w => (w - 1) * riemannZeta w := by
    filter_upwards [compl_singleton_mem_nhds hz] with w hw using regular_zeta_eq_mul hw
  have hfactor : AnalyticAt ℂ (fun w : ℂ => w - 1) z := by fun_prop
  have hζ := analyticOn_riemannZeta z hz
  have hprod : analyticOrderAt (fun w : ℂ => (w - 1) * riemannZeta w) z =
      analyticOrderAt (fun w : ℂ => w - 1) z + analyticOrderAt riemannZeta z :=
    analyticOrderAt_mul hfactor hζ
  rw [analyticOrderNatAt, analyticOrderAt_congr he, hprod,
    hfactor.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hz), zero_add]
  rfl

/-- Count zeros of the Riemann zeta function with multiplicity inside a unit
height window, assuming that its nontrivial zeros are on the critical line. -/
theorem zeta_window_multiplicity (t : ℝ) (Z : Finset ℂ)
    (hRH : ∀ z : ℂ, 0 < z.re → z.re < 1 → riemannZeta z = 0 → z.re = 1 / 2)
    (hZ : ∀ z ∈ Z, 0 < z.re ∧ z.re < 1 ∧ riemannZeta z = 0 ∧ |z.im - t| ≤ 1) :
    (∑ z ∈ Z, (analyticOrderNatAt riemannZeta z : ℝ)) ≤
      (10 / Real.log (23 / 22)) * Real.log (2 + |t|) := by
  let c : ℂ := ⟨3, t⟩
  let U : ℝ := 2 + |t|
  let M : ℝ := 256 * U^2
  have hU : 2 ≤ U := le_add_of_nonneg_right (abs_nonneg t)
  have hUpos : 0 < U := by linarith
  have hM : 1 ≤ M := by dsimp only [M]; nlinarith [sq_nonneg (U-2)]
  have hc : ‖c‖ ≤ 3 + |t| := by simpa [c] using Complex.norm_le_abs_re_add_abs_im c
  have hbound (z : ℂ) (hz : z ∈ sphere c (23 / 8)) : ‖riemannZeta₁ z‖ ≤ M := by
    have hdist : ‖z-c‖ = 23/8 := by simpa only [mem_sphere, dist_eq_norm] using hz
    have hre : |z.re - 3| ≤ 23/8 := by
      simpa only [Complex.sub_re, hdist, c] using Complex.abs_re_le_norm (z-c)
    have hzN : 1 + ‖z‖ ≤ 4 * U := by
      have h := norm_le_norm_sub_add z c
      rw [hdist] at h
      dsimp only [U]
      linarith [abs_nonneg t]
    calc
      _ ≤ 9 * (1 + ‖z‖)^2 := zeta_pole_removed_norm_le_on_strip _ (by linarith [(abs_le.mp hre).1])
      _ ≤ 9 * (4 * U)^2 := by gcongr
      _ ≤ M := by dsimp only [M]; nlinarith [sq_nonneg U]
  have hfac : 2 ≤ ‖c - 1‖ := by
    convert Complex.abs_re_le_norm (c-1) using 1
    norm_num [c]
  have hζ : (1/2 : ℝ) ≤ ‖riemannZeta c‖ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      (half_le_norm_LFunction_of_re_eq_three (1 : DirichletCharacter ℂ 1) (s := c) rfl)
  have hcne : c ≠ 1 := by intro h; have := congrArg Complex.re h; norm_num [c] at this
  have hcen : 1 ≤ ‖riemannZeta₁ c‖ := by
    rw [regular_zeta_eq_mul hcne, norm_mul]
    calc (1:ℝ) = 2 * (1/2) := by norm_num
         _ ≤ _ := mul_le_mul hfac hζ (by norm_num) (norm_nonneg _)
  have hcenpos : 0 < ‖riemannZeta₁ c‖ := zero_lt_one.trans_le hcen
  have hj := window_multiplicity_le_of_circle_bound riemannZeta₁ t M Z
    (fun z hz => ⟨hRH z (hZ z hz).1 (hZ z hz).2.1 (hZ z hz).2.2.1, (hZ z hz).2.2.2⟩)
    (fun z _ => differentiable_riemannZeta₁.analyticAt z)
    (norm_pos_iff.mp hcenpos) hM hbound
  have hlog : Real.log (M / ‖riemannZeta₁ c‖) ≤ 10 * Real.log U := by
    calc
      _ ≤ Real.log M := Real.log_le_log (div_pos (by linarith) hcenpos) (div_le_self (by linarith) hcen)
      _ = 8 * Real.log 2 + 2 * Real.log U := by
        rw [show M = (2 : ℝ)^8 * U^2 by norm_num [M],
          Real.log_mul (by norm_num) (pow_ne_zero _ hUpos.ne'), Real.log_pow, Real.log_pow]
        norm_num
      _ ≤ _ := by linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hU]
  have hden : 0 < Real.log (23/22) := Real.log_pos (by norm_num)
  calc
    _ = ∑ z ∈ Z, (analyticOrderNatAt riemannZeta₁ z : ℝ) := by
      apply Finset.sum_congr rfl
      intro z hz
      have hne : z ≠ 1 := by
        intro h; have := (hZ z hz).2.1; simp [h] at this
      rw [regular_zeta_order hne]
    _ ≤ Real.log (M / ‖riemannZeta₁ c‖) / Real.log (23/22) := by exact_mod_cast hj
    _ ≤ (10 * Real.log U) / Real.log (23/22) := div_le_div_of_nonneg_right hlog hden.le
    _ = _ := by dsimp only [U]; ring

/-- The same logarithmic count for all primitive Dirichlet characters,
including the principal character of conductor one. -/
theorem primitive_character_window_count {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (t : ℝ) (Z : Finset ℂ)
    (hGRH : ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 → z.re = 1 / 2)
    (hZ : ∀ z ∈ Z, 0 < z.re ∧ z.re < 1 ∧ χ.LFunction z = 0 ∧ |z.im - t| ≤ 1) :
    (∑ z ∈ Z, (analyticOrderNatAt χ.LFunction z : ℝ)) ≤
      (10 / Real.log (23 / 22)) * Real.log ((q : ℝ) * (2 + |t|)) := by
  by_cases hχ : χ = 1
  · subst χ
    have h : (1 : DirichletCharacter ℂ q).conductor = q := hprim
    have hq : q = 1 := by simpa only [DirichletCharacter.conductor_one] using h.symm
    subst q
    simp only [DirichletCharacter.LFunction_modOne_eq, Nat.cast_one, one_mul] at *
    exact zeta_window_multiplicity t Z hGRH hZ
  · apply (nonprincipal_character_window_count χ hχ t Z hGRH hZ).trans
    have hq : 1 ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q from q.pos_of_neZero)
    have hlog : 0 ≤ Real.log ((q : ℝ) * (2 + |t|)) :=
      Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq (by linarith [abs_nonneg t]))
    gcongr
    norm_num

theorem primitive_character_full_window_count {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (t : ℝ)
    (hGRH : ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 → z.re = 1 / 2) :
    (∑ z ∈ (finite_character_zeros_in_window χ t 1).toFinset,
        (analyticOrderNatAt χ.LFunction z : ℝ)) ≤
      (10 / Real.log (23 / 22)) * Real.log ((q : ℝ) * (2 + |t|)) := by
  apply primitive_character_window_count χ hprim t _ hGRH
  intro z hz
  obtain ⟨h₀,h₁,hdist,hL⟩ := (finite_character_zeros_in_window χ t 1).mem_toFinset.mp hz
  exact ⟨h₀,h₁,hL,hdist⟩

end

section

open scoped BigOperators

/-- Sum the unit-window counts over the positive and negative heights.
The zero bin uses the real-part lower bound from GRH. -/
private theorem reciprocal_zero_sum_of_windows {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) (hT : 2 ≤ T) (Z : Finset ℂ)
    (hGRH : ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 → z.re = 1 / 2)
    (hZ : ∀ z ∈ Z, 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T ∧ χ.LFunction z = 0)
    (A : ℝ) (hA : 0 ≤ A)
    (hwin : ∀ (t : ℝ) (S : Finset ℂ),
      (∀ z ∈ S, 0 < z.re ∧ z.re < 1 ∧ χ.LFunction z = 0 ∧ |z.im - t| ≤ 1) →
      (∑ z ∈ S, (analyticOrderNatAt χ.LFunction z : ℝ)) ≤ A * Real.log ((q : ℝ) * (2 + |t|))) :
    (∑ z ∈ Z, (analyticOrderNatAt χ.LFunction z : ℝ) / ‖z‖) ≤
      (12 * A) * (Real.log (2 * (q : ℝ) * T)) ^ 2 := by
  classical
  let w (z : ℂ) : ℝ := analyticOrderNatAt χ.LFunction z
  let level (z : ℂ) := ⌊|z.im|⌋₊
  let J := ⌊T⌋₊ + 1
  let shell (j : ℕ) := Z.filter (fun z => level z = j)
  let L := Real.log (2 * (q : ℝ) * T)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q from q.pos_of_neZero)
  have h2T : 2 * T ≤ 2 * (q : ℝ) * T := by
    exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hLhalf : 1 / 2 ≤ L := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show 2 ≤ 2 * (q : ℝ) * T by linarith)
    dsimp only [L]
    linarith only [hh, Real.log_two_gt_d9]
  have hL : 0 ≤ L := by linarith
  have hjT {j : ℕ} (hj : j < J) : (j : ℝ) ≤ T := by
    have hj' : j ≤ ⌊T⌋₊ := Nat.le_of_lt_succ hj
    exact (Nat.cast_le.mpr hj').trans (Nat.floor_le (by linarith))
  have hmaps (z : ℂ) (hz : z ∈ Z) : level z ∈ Finset.range J :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono (hZ z hz).2.2.1))
  have hloc {j : ℕ} {z : ℂ} (hz : z ∈ shell j) :
      z ∈ Z ∧ (j : ℝ) ≤ |z.im| ∧ |z.im| < (j : ℝ) + 1 := by
    obtain ⟨hzZ, hj⟩ := Finset.mem_filter.mp hz
    rw [← hj]
    exact ⟨hzZ, Nat.floor_le (abs_nonneg _), Nat.lt_floor_add_one _⟩
  have hcount (j : ℕ) (hj : j < J) : (∑ z ∈ shell j, w z) ≤ 2 * A * L := by
    have hlog : Real.log ((q : ℝ) * (2 + (j : ℝ))) ≤ L := by
      apply Real.log_le_log (by positivity)
      calc
        _ ≤ (q : ℝ) * (2 * T) :=
          mul_le_mul_of_nonneg_left (by linarith [hjT hj]) (by positivity)
        _ = _ := by ring
    have hw (S : Finset ℂ) (t : ℝ) (ht : |t| = (j : ℝ))
        (hS : ∀ z ∈ S, z ∈ Z ∧ |z.im - t| ≤ 1) : (∑ z ∈ S, w z) ≤ A * L := by
      have hc := hwin t S (fun z hz =>
        let v := hZ z (hS z hz).1
        ⟨v.1, v.2.1, v.2.2.2, (hS z hz).2⟩)
      rw [ht] at hc
      exact hc.trans (mul_le_mul_of_nonneg_left hlog hA)
    have hp : (∑ z ∈ (shell j).filter (fun z => 0 ≤ z.im), w z) ≤ A * L := by
      apply hw _ j (abs_of_nonneg (Nat.cast_nonneg _))
      intro z hz
      obtain ⟨hs, him⟩ := Finset.mem_filter.mp hz
      obtain ⟨hzZ, hlo, hhi⟩ := hloc hs
      rw [abs_of_nonneg him] at hlo hhi
      exact ⟨hzZ, abs_le.mpr ⟨by linarith, by linarith⟩⟩
    have hn : (∑ z ∈ (shell j).filter (fun z => ¬0 ≤ z.im), w z) ≤ A * L := by
      apply hw _ (-(j : ℝ)) (by simp)
      intro z hz
      obtain ⟨hs, him⟩ := Finset.mem_filter.mp hz
      obtain ⟨hzZ, hlo, hhi⟩ := hloc hs
      rw [abs_of_neg (lt_of_not_ge him)] at hlo hhi
      exact ⟨hzZ, abs_le.mpr ⟨by linarith, by linarith⟩⟩
    rw [← Finset.sum_filter_add_sum_filter_not (shell j) (fun z => 0 ≤ z.im) w]
    linarith only [hp, hn]
  have hbin (j : ℕ) (hj : j < J) :
      (∑ z ∈ shell j, w z / ‖z‖) ≤ (4 * A * L) * ((j : ℝ) + 1)⁻¹ := by
    have hjpos : 0 < (j : ℝ) + 1 := by positivity
    have hi (z : ℂ) (hz : z ∈ shell j) : ‖z‖⁻¹ ≤ 2 / ((j : ℝ) + 1) := by
      obtain ⟨hzZ, hlo, _⟩ := hloc hz
      obtain ⟨hz0, hz1, _, hroot⟩ := hZ z hzZ
      have hre := Complex.abs_re_le_norm z
      rw [hGRH z hz0 hz1 hroot] at hre
      norm_num at hre
      have hnorm : 0 < ‖z‖ := by linarith
      rw [← one_div, div_le_div_iff₀ hnorm hjpos]
      rcases Nat.eq_zero_or_pos j with rfl | hj'
      · norm_num
        linarith
      · have hj1 : 1 ≤ (j : ℝ) := by exact_mod_cast hj'
        linarith only [hj1, hlo, Complex.abs_im_le_norm z]
    calc
      _ ≤ ∑ z ∈ shell j, w z * (2 / ((j : ℝ) + 1)) := by
        apply Finset.sum_le_sum
        intro z hz
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (hi z hz) (Nat.cast_nonneg _)
      _ = (∑ z ∈ shell j, w z) * (2 / ((j : ℝ) + 1)) := (Finset.sum_mul ..).symm
      _ ≤ (2 * A * L) * (2 / ((j : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right (hcount j hj) (by positivity)
      _ = _ := by ring
  have hJ : (J : ℝ) ≤ 2 * (q : ℝ) * T := by
    have hf := Nat.floor_le (show 0 ≤ T by linarith)
    dsimp only [J]
    rw [Nat.cast_add_one]
    linarith
  have hharm : (harmonic J : ℝ) ≤ 3 * L := by
    have hJpos : (0 : ℝ) < J := by dsimp [J]; positivity
    have hlJ : Real.log (J : ℝ) ≤ L := Real.log_le_log hJpos hJ
    linarith only [harmonic_le_one_add_log J, hlJ, hLhalf]
  calc
    _ = ∑ j ∈ Finset.range J, ∑ z ∈ shell j, w z / ‖z‖ :=
      (Finset.sum_fiberwise_of_maps_to hmaps (fun z => w z / ‖z‖)).symm
    _ ≤ ∑ j ∈ Finset.range J, (4 * A * L) * ((j : ℝ) + 1)⁻¹ :=
      Finset.sum_le_sum fun j hj => hbin j (Finset.mem_range.mp hj)
    _ = (4 * A * L) * (harmonic J : ℝ) := by
      rw [← Finset.mul_sum]
      simp [harmonic]
    _ ≤ (4 * A * L) * (3 * L) := mul_le_mul_of_nonneg_left hharm (by positivity)
    _ = _ := by dsimp only [L]; ring



/-- For primitive characters the same argument includes the zeros of the
Riemann zeta function at conductor one. -/
theorem primitive_reciprocal_zero_sum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (T : ℝ) (hT : 2 ≤ T) (Z : Finset ℂ)
    (hGRH : ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 → z.re = 1 / 2)
    (hZ : ∀ z ∈ Z, 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T ∧ χ.LFunction z = 0) :
    (∑ z ∈ Z, (analyticOrderNatAt χ.LFunction z : ℝ) / ‖z‖) ≤
      (120 / Real.log (23 / 22)) * (Real.log (2 * (q : ℝ) * T)) ^ 2 := by
  have h := reciprocal_zero_sum_of_windows χ T hT Z hGRH hZ
    (10 / Real.log (23 / 22)) (div_nonneg (by norm_num) (Real.log_nonneg (by norm_num)))
    (fun t S => primitive_character_window_count χ hprim t S hGRH)
  convert h using 1
  ring


end

section

open Complex MeasureTheory Filter ArithmeticFunction DirichletCharacter Finset

private noncomputable def perronLine (t : ℝ) : ℂ := 2 + (t : ℂ) * I

private theorem perronLine_re (t : ℝ) : (perronLine t).re = 2 := by simp [perronLine]

private noncomputable def perronKernelAt (s : ℂ) := 1 / (s * (s + 1))

private theorem perronKernel_integrable : Integrable (fun t : ℝ => perronKernelAt (perronLine t)) := by
  apply integrable_inv_one_add_sq.mono'
  · exact (by unfold perronKernelAt perronLine; fun_prop : Measurable _).aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  have h1 : ‖perronLine t‖ ^ 2 = 2 * 2 + t * t := by
    simpa [perronLine, Complex.normSq_apply] using Complex.sq_norm (perronLine t)
  have h2 : ‖perronLine t + 1‖ ^ 2 = (2+1) * (2+1) + t * t := by
    simpa [perronLine, Complex.normSq_apply] using Complex.sq_norm (perronLine t + 1)
  have hn : ‖perronLine t‖ ≤ ‖perronLine t + 1‖ := by nlinarith [norm_nonneg (perronLine t + 1)]
  rw [perronKernelAt, norm_div, norm_one, norm_mul, one_div]
  apply inv_anti₀ (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hn (norm_nonneg (perronLine t))]

theorem smoothed_lseries_perron (a : ℕ → ℂ) (ha₀ : a 0 = 0) (ha : LSeriesSummable a 2)
    {x : ℝ} (hx : 0 < x) :
    mellinInv 2 (fun s => LSeries a s * (1 / (s * (s + 1)))) x =
      ∑' n : ℕ, a n * perronWeight (n * x) := by
  let F (n : ℕ) (t : ℝ) := ((x : ℂ) ^ (-perronLine t) * perronKernelAt (perronLine t)) *
      LSeries.term a (perronLine t) n
  let b (n : ℕ) := x ^ (-2 : ℝ) * ‖LSeries.term a 2 n‖
  have hnorm (n : ℕ) (t : ℝ) : ‖F n t‖ = b n * ‖perronKernelAt (perronLine t)‖ := by
    simp only [F, b, norm_mul, norm_cpow_eq_rpow_re_of_pos hx, neg_re, perronLine_re,
      LSeries.norm_term_eq, re_ofNat]
    ring
  have hmeas (n : ℕ) : Measurable (F n) := by
    simp only [F, perronKernelAt, perronLine, LSeries.term_def₀ ha₀]
    fun_prop
  have hi (n : ℕ) : Integrable (F n) := by
    apply (perronKernel_integrable.norm.const_mul (b n)).mono' (hmeas n).aestronglyMeasurable
    exact Eventually.of_forall fun t => (hnorm n t).le
  have hs : Summable (fun n => ∫ t : ℝ, ‖F n t‖) := by
    simp_rw [hnorm, integral_const_mul]
    exact (ha.norm.mul_left (x ^ (-2 : ℝ))).mul_right _
  have hsum (t : ℝ) : (∑' n, F n t) =
      (x : ℂ) ^ (-perronLine t) * (LSeries a (perronLine t) * perronKernelAt (perronLine t)) := by
    rw [show (∑' n, F n t) = _ from tsum_mul_left]
    change _ * LSeries a (perronLine t) = _
    ring
  have hsingle (n : ℕ) : (1 / (2 * Real.pi) : ℝ) • (∫ t : ℝ, F n t) =
      a n * perronWeight (n * x) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [F, ha₀]
    have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hfun (t : ℝ) : F n t = a n * ((((n : ℝ) * x : ℝ) : ℂ) ^ (-perronLine t) *
          perronKernelAt (perronLine t)) := by
      rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hn'.le hx.le]
      simp only [F, LSeries.term_def₀ ha₀, Complex.ofReal_natCast]
      ring
    rw [← perronWeight_inversion (mul_pos hn' hx)]
    unfold mellinInv
    simp_rw [hfun]
    rw [integral_const_mul]
    change _ • (a n * _) = a n * (_ • _)
    rw [mul_smul_comm]
    rfl
  have hsm := (hasSum_integral_of_summable_integral_norm hi hs).const_smul
    (1 / (2 * Real.pi) : ℝ)
  simp_rw [hsingle, hsum] at hsm
  exact hsm.tsum_eq.symm

theorem twisted_smoothed_perron {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {X : ℝ} (hX : 0 < X) :
    mellinInv 2 (fun s : ℂ => (-deriv (LFunction χ) s / LFunction χ s) *
      (1 / (s * (s + 1)))) (1 / X) =
    ∑ n ∈ Icc 1 ⌊X⌋₊, χ (n : ZMod q) * (vonMangoldt n : ℂ) * (1 - (n : ℂ) / (X : ℂ)) := by
  let a (n : ℕ) := χ (n : ZMod q) * (vonMangoldt n : ℂ)
  have ha₀ : a 0 = 0 := by simp [a]
  have ha : LSeriesSummable a 2 := LSeriesSummable_twist_vonMangoldt χ (by norm_num)
  calc
    _ = mellinInv 2 (fun s => LSeries a s * (1 / (s * (s + 1)))) (1 / X) := by
      unfold mellinInv
      congr 1
      apply integral_congr_ae
      apply Eventually.of_forall
      intro t
      have hs : 1 < (((2 : ℝ) : ℂ) + (t : ℂ) * I).re := by norm_num
      dsimp only
      rw [deriv_LFunction_eq_deriv_LSeries χ hs, LFunction_eq_LSeries χ hs,
        ← LSeries_twist_vonMangoldt_eq χ hs]
      rfl
    _ = ∑' n : ℕ, a n * perronWeight ((n : ℝ) * (1 / X)) :=
      smoothed_lseries_perron a ha₀ ha (one_div_pos.mpr hX)
    _ = _ := by
      rw [tsum_eq_sum (s := Icc 1 ⌊X⌋₊) (fun n hn => ?_)]
      · apply sum_congr rfl
        intro n hn
        obtain ⟨hnp, hnf⟩ := mem_Icc.mp hn
        have hnℝ : 0 < (n : ℝ) := Nat.cast_pos.mpr hnp
        have hnx : (n : ℝ) ≤ X := (Nat.le_floor_iff hX.le).mp hnf
        have hm : (n : ℝ) * (1 / X) ∈ Set.Ioc (0 : ℝ) 1 := by
          rw [mul_one_div]
          exact ⟨div_pos hnℝ hX, (div_le_one hX).mpr hnx⟩
        rw [perronWeight, Set.indicator_of_mem hm]
        simp only [mul_one_div, Complex.ofReal_div, Complex.ofReal_natCast, a]
      · by_cases hz : n = 0
        · simp [hz, ha₀]
        · have hn' : ⌊X⌋₊ < n := by
            by_contra! h
            exact hn (mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hz, h⟩)
          have hx : X < (n : ℝ) := (Nat.floor_lt hX.le).mp hn'
          have hm : (n : ℝ) * (1 / X) ∉ Set.Ioc (0 : ℝ) 1 := by
            intro h
            rw [mul_one_div] at h
            exact (not_le.mpr hx) ((div_le_one hX).mp h.2)
          rw [perronWeight, Set.indicator_of_notMem hm, mul_zero]

end

section

open Filter Set
open scoped Topology

/-- Subtracting the pole of the logarithmic derivative at a zero of finite
order leaves a holomorphic germ. -/
theorem logDeriv_principal_part {f : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ)
    (hord : analyticOrderAt f ρ ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧
      ∀ᶠ z in 𝓝[≠] ρ, logDeriv f z = (analyticOrderNatAt f ρ : ℂ) / (z - ρ) + g z := by
  let m := analyticOrderNatAt f ρ
  obtain ⟨u, hanu, hu, heq⟩ := hf.analyticOrderAt_ne_top.mp hord
  refine ⟨logDeriv u, hanu.deriv.div hanu hu, ?_⟩
  have hprod : f =ᶠ[𝓝 ρ] fun z => (z - ρ)^m * u z := heq
  filter_upwards [(logDeriv_congr_nhds hprod).filter_mono nhdsWithin_le_nhds,
    hanu.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    (hanu.continuousAt.eventually_ne hu).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz haz hn hne
  have hzρ : z - ρ ≠ 0 := sub_ne_zero.mpr hne
  rw [hz, logDeriv_fun_mul (f := fun v : ℂ => (v - ρ) ^ m) (g := u) z
    (pow_ne_zero _ hzρ) hn (by fun_prop) haz.differentiableAt,
    logDeriv_fun_pow (f := fun v : ℂ => v - ρ) (by fun_prop)]
  simp [logDeriv_apply, m, div_eq_mul_inv]


end

section

open scoped BigOperators
open ArithmeticFunction DirichletCharacter

/-- The triangularly weighted sum with unnormalised weight `X - n`. -/
noncomputable def triangularTwist {q : ℕ} (χ : DirichletCharacter ℂ q) (X : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (X + 1),
    χ (n : ZMod q) * (vonMangoldt n : ℂ) * ((X : ℂ) - n)


/-- The unnormalised triangular sum is the cutoff times its Perron integral. -/
theorem triangularTwist_eq_mellinInv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (X : ℕ) (hX : 0 < X) :
    triangularTwist χ X = (X : ℂ) * mellinInv 2 (fun s : ℂ =>
      (-deriv χ.LFunction s / χ.LFunction s) * (1 / (s * (s + 1)))) (1 / (X : ℝ)) := by
  have hc : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  rw [twisted_smoothed_perron χ (by exact_mod_cast hX), Nat.floor_natCast, Finset.mul_sum]
  let a (n : ℕ) : ℂ := χ (n : ZMod q) * (vonMangoldt n : ℂ)
  calc
    _ = ∑ n ∈ Finset.Icc 1 X, a n * ((X : ℂ) - n) := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sub _ (by omega)]
      simp [triangularTwist, a]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _
      simp only [a, Complex.ofReal_natCast]
      field_simp


end

section

/-- Choose a height within one unit of T, quantitatively separated from
every member of a given finite set of ordinates. -/
theorem exists_height_avoiding (B : Finset ℝ) (T : ℝ) :
    ∃ t ∈ Set.Icc T (T + 1), ∀ b ∈ B, 1 / (3 * (B.card + 1 : ℝ)) ≤ |t - b| := by
  classical
  let N : ℝ := B.card + 1
  have hN : 0 < N := by dsimp [N]; positivity
  let grid (j : Fin (B.card + 1)) : ℝ := T + (j.val : ℝ) / N
  have hI (j) : grid j ∈ Set.Icc T (T + 1) := by
    constructor
    · exact le_add_of_nonneg_right (div_nonneg (by positivity) hN.le)
    · change T + (j.val : ℝ) / N ≤ T + 1
      apply add_le_add_right
      apply (div_le_one hN).2
      dsimp [N]
      exact_mod_cast j.isLt.le
  by_contra! hall
  have hchoice (j) : ∃ b : B, |grid j - (b : ℝ)| < 1 / (3 * N) := by
    obtain ⟨b, hb, h⟩ := hall (grid j) (hI j)
    exact ⟨⟨b, hb⟩, h⟩
  choose f hf using hchoice
  have hinj : Function.Injective f := by
    intro i j hij
    have ha := (abs_lt.mp (hf i))
    have hb := (abs_lt.mp (hf j))
    rw [hij] at ha
    have hdiff : |grid i - grid j| < 1 / N := by
      have hthird : (3 : ℝ) * (1 / (3 * N)) = 1 / N := by field_simp
      rw [abs_lt]
      constructor <;> linarith [one_div_pos.mpr hN]
    have hid : grid i - grid j = ((i.val : ℝ) - j.val) / N := by simp [grid]; ring
    rw [hid, abs_div, abs_of_pos hN, div_lt_div_iff_of_pos_right hN, abs_lt] at hdiff
    have hi : i.val < j.val + 1 := by exact_mod_cast (show (i.val : ℝ) < j.val + 1 by linarith [hdiff.2])
    have hj : j.val < i.val + 1 := by exact_mod_cast (show (j.val : ℝ) < i.val + 1 by linarith [hdiff.1])
    exact Fin.ext (by omega)
  have hcard := Fintype.card_le_of_injective f hinj
  simp at hcard

end

section

open scoped BigOperators Topology
open Filter Metric

/-- Divide out the prescribed multiplicities of the zeros in the inner
closed disk. The corrected quotient extends analytically across every
removed zero, remains analytic on the outer disk, and has no inner zeros. -/
theorem remove_prescribed_disk_zeros (f : ℂ → ℂ) (c : ℂ) (r R : ℝ)
    (hr : 0 ≤ r) (hrR : r ≤ R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hc : f c ≠ 0) (Z : Finset ℂ)
    (hZ : ∀ z : ℂ, z ∈ Z ↔ z ∈ closedBall c r ∧ f z = 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall c R) ∧
      (∀ z ∈ closedBall c r, g z ≠ 0) ∧
      ∀ w, f w = (∏ z ∈ Z, (w - z) ^ analyticOrderNatAt f z) * g w := by
  classical
  have hR := hr.trans hrR
  have hcenter : c ∈ closedBall c R := by simpa using hR
  have hfinite := (hf.exists_analyticOrderAt_ne_top_iff_forall (isConnected_closedBall hR)).mp
    ⟨⟨c, hcenter⟩, by rw [(hf c hcenter).analyticOrderAt_eq_zero.mpr hc]; simp⟩
  let m (z : ℂ) := analyticOrderNatAt f z
  let P (w : ℂ) := ∏ z ∈ Z, (w - z) ^ m z
  let Q (z w : ℂ) := ∏ a ∈ Z.erase z, (w - a) ^ m a
  have hsplit {z : ℂ} (hz : z ∈ Z) (w : ℂ) : P w = (w - z) ^ m z * Q z w :=
    (Z.mul_prod_erase (fun a => (w - a) ^ m a) hz).symm
  have hprod {F : Finset ℂ} {w : ℂ} (hw : w ∉ F) :
      (∏ a ∈ F, (w - a) ^ m a) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    exact pow_ne_zero _ (sub_ne_zero.mpr (fun he => hw (he ▸ ha)))
  have hprodAn (F : Finset ℂ) (w : ℂ) : AnalyticAt ℂ (fun b => ∏ a ∈ F, (b - a) ^ m a) w := by
    fun_prop
  have hlocal (z : ℂ) (hz : z ∈ Z) :
      ∃ u : ℂ → ℂ, AnalyticAt ℂ u z ∧ u z ≠ 0 ∧
        ∀ᶠ w in 𝓝 z, f w = (w - z) ^ m z * u w := by
    have hzR := closedBall_subset_closedBall hrR ((hZ z).mp hz).1
    exact (hf z hzR).analyticOrderAt_ne_top.mp (hfinite ⟨z, hzR⟩)
  choose u hu hune hfac using hlocal
  let g (w : ℂ) := if hw : w ∈ Z then u w hw w / Q w w else f w / P w
  refine ⟨g, ?_, ?_, ?_⟩
  · intro z hzR
    by_cases hz : z ∈ Z
    · have hQ : Q z z ≠ 0 := hprod (Finset.notMem_erase _ _)
      apply ((hu z hz).div (hprodAn (Z.erase z) z) hQ).congr
      have havoid : ∀ᶠ w in 𝓝 z, w ∉ Z.erase z :=
        (Z.erase z).isClosed.isOpen_compl.mem_nhds (Finset.notMem_erase _ _)
      filter_upwards [havoid, hfac z hz] with w hw hfw
      change u z hz w / Q z w = g w
      by_cases hwz : w = z
      · subst w
        simp [g, hz]
      · have hwZ : w ∉ Z := fun h => hw (Finset.mem_erase.mpr ⟨hwz, h⟩)
        have hpow := pow_ne_zero (m z) (sub_ne_zero.mpr hwz)
        simp only [g, dite_eq_right hwZ, hfw, hsplit hz w]
        field_simp
    · apply ((hf z hzR).div (hprodAn Z z) (hprod hz)).congr
      filter_upwards [Z.isClosed.isOpen_compl.mem_nhds (show z ∉ Z from hz)] with w hw
      change w ∉ Z at hw
      simp [g, hw, P]
  · intro z hzr
    by_cases hz : z ∈ Z
    · simp only [g, dite_eq_left hz]
      exact div_ne_zero (hune z hz) (hprod (Finset.notMem_erase _ _))
    · simp only [g, dite_eq_right hz]
      exact div_ne_zero (fun he => hz ((hZ z).mpr ⟨hzr, he⟩)) (hprod hz)
  · intro w
    change f w = P w * g w
    by_cases hw : w ∈ Z
    · have h := (hfac w hw).self_of_nhds
      rw [h, hsplit hw w]
      simp only [g, dite_eq_left hw]
      have hQ : Q w w ≠ 0 := hprod (Finset.notMem_erase _ _)
      field_simp
    · simp only [g, dite_eq_right hw]
      have hP : P w ≠ 0 := hprod hw
      field_simp

/-- A finite list of all inner zeros and its exact analytic factorization
exist on every nested pair of closed disks with a nonzero central value. -/
theorem remove_disk_zeros (f : ℂ → ℂ) (c : ℂ) (r R : ℝ)
    (hr : 0 ≤ r) (hrR : r ≤ R) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0) :
    ∃ (Z : Finset ℂ) (g : ℂ → ℂ), (∀ z : ℂ, z ∈ Z ↔ z ∈ closedBall c r ∧ f z = 0) ∧
      AnalyticOnNhd ℂ g (closedBall c R) ∧ (∀ z ∈ closedBall c r, g z ≠ 0) ∧
      ∀ w, f w = (∏ z ∈ Z, (w - z) ^ analyticOrderNatAt f z) * g w := by
  classical
  have hrAn : AnalyticOnNhd ℂ f (closedBall c r) := hf.mono (closedBall_subset_closedBall hrR)
  have hd := hrAn.preimage_zero_mem_codiscreteWithin hc (mem_closedBall_self hr)
    (isConnected_closedBall hr)
  have hfinite : {z ∈ closedBall c r | f z = 0}.Finite :=
    ((isCompact_closedBall c r).finite_sdiff_of_mem_codiscreteWithin hd).subset
      (fun z hz => ⟨hz.1, by simp [hz.2]⟩)
  let Z := hfinite.toFinset
  have hZ (z : ℂ) : z ∈ Z ↔ z ∈ closedBall c r ∧ f z = 0 := hfinite.mem_toFinset
  obtain ⟨g, han, hnz, hfac⟩ := remove_prescribed_disk_zeros f c r R hr hrR hf hc Z hZ
  exact ⟨Z, g, hZ, han, hnz, hfac⟩

end

section

open Complex Metric Set MeromorphicOn

theorem logDeriv_bound_nonvanishing_disk (f : ℂ → ℂ) {M : ℝ} (hM : 0 < M)
    (hf : DifferentiableOn ℂ f (ball 0 (23 / 8)))
    (hn : ∀ z ∈ ball (0 : ℂ) (23 / 8), f z ≠ 0)
    (hbound : ∀ z ∈ ball (0 : ℂ) (23 / 8), ‖f z‖ ≤ ‖f 0‖ * Real.exp M)
    {z : ℂ} (hz : ‖z‖ ≤ 11 / 4) :
    ‖logDeriv f z‖ ≤ 1440 * M := by
  have h0 : (0 : ℂ) ∈ ball 0 (23 / 8) := mem_ball_self (by norm_num)
  have hh : DifferentiableOn ℂ (logDeriv f) (ball 0 (23 / 8)) :=
    (hf.deriv isOpen_ball).div hf hn
  obtain ⟨g, hg₀, hg⟩ := hh.isExactOn_ball.with_val_at (0 : ℂ) 0
  have hgd : DifferentiableOn ℂ g (ball 0 (23 / 8)) :=
    fun x hx => (hg x hx).differentiableAt.differentiableWithinAt
  have heg : DifferentiableOn ℂ (fun x => Complex.exp (g x)) (ball 0 (23 / 8)) :=
    fun x hx => (hg x hx).cexp.differentiableAt.differentiableWithinAt
  have hrel := (logDeriv_eqOn_iff hf heg isOpen_ball (convex_ball _ _).isPreconnected
    (fun x _ => Complex.exp_ne_zero (g x)) hn).mp
  obtain ⟨k, hk, hfac⟩ := hrel (by
    intro x hx
    rw [logDeriv_apply (fun x => Complex.exp (g x)), (hg x hx).cexp.deriv]
    field_simp)
  have hk₀ : f 0 = k := by simpa [hg₀] using hfac h0
  have hre (w : ℂ) (hw : w ∈ ball 0 (23 / 8)) : (g w).re ≤ M := by
    apply Real.exp_le_exp.mp
    have heq : f w = f 0 * Complex.exp (g w) := by simpa [hk₀] using hfac hw
    have h := hbound w hw
    rw [heq, norm_mul, Complex.norm_exp] at h
    exact (mul_le_mul_iff_right₀ (norm_pos_iff.mpr (hn 0 h0))).mp h
  have hgeo (w : ℂ) (hw : w ∈ closedBall z (1 / 16)) : ‖w‖ ≤ 45 / 16 := by
    have hs : ‖w - z‖ ≤ 1 / 16 := by simpa [mem_closedBall, dist_eq_norm] using hw
    linarith [norm_le_norm_sub_add w z]
  have hsub : closedBall z (1 / 16) ⊆ ball (0 : ℂ) (23 / 8) := by
    intro w hw
    rw [mem_ball_zero_iff]
    linarith [hgeo w hw]
  have hC : ∀ w ∈ sphere z (1 / 16), ‖g w‖ ≤ 90 * M := by
    intro w hw
    have hb := sphere_subset_closedBall hw
    have hle := hgeo w hb
    have hd : 0 < 23 / 8 - ‖w‖ := by linarith
    apply (borelCaratheodory_zero hM hgd (fun w hw => hre w hw) (by norm_num) (hsub hb) hg₀).trans
    apply (div_le_iff₀ hd).2
    nlinarith [mul_nonneg hM.le (sub_nonneg.mpr hle)]
  have hzb : z ∈ ball (0 : ℂ) (23 / 8) := mem_ball_zero_iff.mpr (by linarith)
  rw [← (hg z hzb).deriv]
  apply (Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ) < 1/16)
    (hgd.diffContOnCl_ball hsub) hC).trans
  linarith

theorem logDeriv_bound_after_removing_zeros (f g : ℂ → ℂ) (Z : Finset ℂ) (m : ℂ → ℕ)
    (hroots : ∀ ρ ∈ Z, ‖ρ‖ ≤ 23 / 8)
    (hfac : ∀ w ∈ closedBall (0 : ℂ) (47 / 16),
      f w = (∏ ρ ∈ Z, (w - ρ) ^ m ρ) * g w)
    (hg : DiffContOnCl ℂ g (ball 0 (47 / 16)))
    (hgn : ∀ w ∈ ball (0 : ℂ) (23 / 8), g w ≠ 0)
    {M : ℝ} (hM : 0 < M)
    (hfbound : ∀ w ∈ sphere (0 : ℂ) (47 / 16), ‖f w‖ ≤ ‖f 0‖ * Real.exp M)
    {z : ℂ} (hz : ‖z‖ ≤ 11 / 4) (hzZ : z ∉ Z) :
    ‖logDeriv f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)‖ ≤
      1440 * (M + (∑ ρ ∈ Z, m ρ : ℕ) * Real.log 48) := by
  classical
  let P : ℂ → ℂ := fun w => ∏ ρ ∈ Z, (w - ρ) ^ m ρ
  let N := ∑ ρ ∈ Z, m ρ
  have hcenter : ‖f 0‖ ≤ (3 : ℝ) ^ N * ‖g 0‖ := by
    rw [hfac 0 (mem_closedBall_self (by norm_num)), norm_mul, norm_prod,
      ← Finset.prod_pow_eq_pow_sum Z m (3 : ℝ)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro ρ hρ
    rw [norm_pow, zero_sub, norm_neg]
    exact pow_le_pow_left₀ (norm_nonneg _) (by linarith [hroots ρ hρ]) _
  have hboundary (w : ℂ) (hw : w ∈ sphere 0 (47 / 16)) :
      ‖g w‖ ≤ ‖g 0‖ * Real.exp (M + (N : ℝ) * Real.log 48) := by
    have hnw : ‖w‖ = 47/16 := by simpa [mem_sphere, dist_zero_right] using hw
    have hP : (1/16 : ℝ) ^ N ≤ ‖P w‖ := by
      rw [show ‖P w‖ = _ from norm_prod .., ← Finset.prod_pow_eq_pow_sum Z m (1/16 : ℝ)]
      apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
      intro ρ hρ
      rw [norm_pow]
      apply pow_le_pow_left₀ (by norm_num)
      linarith [norm_le_norm_sub_add w ρ, hroots ρ hρ]
    have hU := hfbound w hw
    rw [hfac w (sphere_subset_closedBall hw), norm_mul] at hU
    have hval : (1/16 : ℝ) ^ N * ‖g w‖ ≤ (3 : ℝ) ^ N * ‖g 0‖ * Real.exp M :=
      (mul_le_mul_of_nonneg_right hP (norm_nonneg _)).trans
        (hU.trans (mul_le_mul_of_nonneg_right hcenter (Real.exp_pos M).le))
    rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 48)]
    apply (mul_le_mul_iff_right₀ (show 0 < (1 / 16 : ℝ) ^ N by positivity)).mp
    calc
      _ ≤ _ := hval
      _ = _ := by
        have hk : ((1/16 : ℝ) ^ N) * (48 : ℝ) ^ N = 3 ^ N := by rw [← mul_pow]; norm_num
        linear_combination -(‖g 0‖ * Real.exp M) * hk
  have hUpos : 0 < M + (N : ℝ) * Real.log 48 := by
    exact add_pos_of_pos_of_nonneg hM (mul_nonneg (Nat.cast_nonneg N) (Real.log_nonneg (by norm_num)))
  have hsubset : ball (0 : ℂ) (23 / 8) ⊆ ball 0 (47 / 16) := ball_subset_ball (by norm_num)
  have hregular := logDeriv_bound_nonvanishing_disk g hUpos (hg.1.mono hsubset) hgn
    (fun w hw => norm_le_of_forall_mem_frontier_norm_le isBounded_ball hg
      (fun v hv => hboundary v (by rwa [frontier_ball (0 : ℂ) (by norm_num : (47 / 16 : ℝ) ≠ 0)] at hv))
      (subset_closure (hsubset hw))) hz
  have hzin : z ∈ ball (0 : ℂ) (23/8) := mem_ball_zero_iff.mpr (by linarith)
  have heq : f =ᶠ[nhds z] fun w => P w * g w := by
    filter_upwards [isOpen_ball.mem_nhds (hsubset hzin)] with w hw
    exact hfac w (ball_subset_closedBall hw)
  have hpz (ρ : ℂ) (hρ : ρ ∈ Z) : z - ρ ≠ 0 := sub_ne_zero.mpr (fun e => hzZ (e ▸ hρ))
  have hPdiff : DifferentiableAt ℂ P z := by dsimp [P]; fun_prop
  have hPz : P z ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun ρ hρ => pow_ne_zero _ (hpz ρ hρ))
  have hPder : logDeriv P z = ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) := by
    rw [show logDeriv P z = _ from logDeriv_fun_prod
      (f := fun ρ (w : ℂ) => (w - ρ) ^ m ρ) (fun ρ hρ => pow_ne_zero _ (hpz ρ hρ))
      (fun _ _ => by fun_prop)]
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [logDeriv_fun_pow (f := fun w : ℂ => w - ρ) (by fun_prop)]
    simp [logDeriv_apply, div_eq_mul_inv]
  rw [(logDeriv_congr_nhds heq).eq_of_nhds,
    logDeriv_fun_mul z hPz (hgn z hzin) hPdiff
      (hg.1.differentiableAt (isOpen_ball.mem_nhds (hsubset hzin))), hPder, add_sub_cancel_left]
  exact hregular

theorem inner_disk_multiplicity_bound {f : ℂ → ℂ} (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, ‖ρ‖ ≤ 23 / 8)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 (47 / 16))) (hf₀ : f 0 ≠ 0)
    {B : ℝ} (hB : 1 ≤ B) (hboundary : ∀ z ∈ sphere 0 (47 / 16), ‖f z‖ ≤ B) :
    ((∑ ρ ∈ Z, analyticOrderNatAt f ρ : ℕ) : ℝ) ≤
      Real.log (B / ‖f 0‖) / Real.log (47 / 46) := by
  classical
  let K := closedBall (0 : ℂ) (23 / 8)
  let d := MeromorphicOn.divisor f K
  have ha : AnalyticOnNhd ℂ f K := hf.mono (closedBall_subset_closedBall (by norm_num))
  have hs := d.finiteSupport (isCompact_closedBall 0 (23 / 8))
  let U := Z ∪ hs.toFinset
  have hu : Function.support d ⊆ (U : Set ℂ) :=
    fun _ hi => Finset.mem_union_right _ (hs.mem_toFinset.mpr hi)
  have hcount : ((∑ ρ ∈ Z, analyticOrderNatAt f ρ : ℕ) : ℤ) ≤ ∑ᶠ w, d w := by
    rw [finsum_eq_sum_of_support_subset _ hu, Nat.cast_sum]
    calc
      _ = ∑ w ∈ Z, d w := by
        apply Finset.sum_congr rfl
        intro w hw
        change _ = MeromorphicOn.divisor f K w
        rw [ha.divisor_apply (mem_closedBall_zero_iff.mpr (hZ w hw))]
        unfold analyticOrderNatAt
        cases h : analyticOrderAt f w using ENat.recTopCoe <;> simp
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun w _ _ => ha.divisor_nonneg w)
  have hJ := AnalyticOnNhd.sum_divisor_le (c := (0 : ℂ)) (r := (23/8 : ℝ))
    (R := (47/16 : ℝ)) (M := B) (by norm_num) (by norm_num) hB
    (by simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 47 / 16)] using hf) hf₀
    (by simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 47 / 16)] using hboundary)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 23 / 8),
    show (47 / 16 : ℝ) / (23 / 8) = 47 / 46 by norm_num] at hJ
  exact le_trans (by exact_mod_cast hcount) hJ

theorem local_logDeriv_bound_of_distance (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 (47/16))) (hf₀ : f 0 ≠ 0)
    {B D δ : ℝ} (hB : 1 ≤ B) (hD : 0 < D) (hδ : 0 < δ)
    (hboundary : ∀ w ∈ sphere 0 (47 / 16), ‖f w‖ ≤ B)
    (hlog : Real.log (B / ‖f 0‖) ≤ D)
    {z : ℂ} (hz : ‖z‖ ≤ 11/4)
    (hsep : ∀ ρ ∈ closedBall (0 : ℂ) (23/8), f ρ = 0 → δ ≤ ‖z-ρ‖) :
    ‖logDeriv f z‖ ≤ (1440 + (1440 * Real.log 48 + 1/δ) / Real.log (47/46)) * D := by
  classical
  obtain ⟨Z, g, hZ, hg, hgn, hfac⟩ :=
    remove_disk_zeros f 0 (23 / 8) (47 / 16) (by norm_num) (by norm_num) hf hf₀
  let N := ∑ ρ ∈ Z, analyticOrderNatAt f ρ
  have hr (ρ) (hρ : ρ ∈ Z) := (hZ ρ).mp hρ
  have hd (ρ) (hρ : ρ ∈ Z) : δ ≤ ‖z-ρ‖ := hsep ρ (hr ρ hρ).1 (hr ρ hρ).2
  have hroot (ρ) (hρ : ρ ∈ Z) : ‖ρ‖ ≤ 23 / 8 := mem_closedBall_zero_iff.mp (hr ρ hρ).1
  have hfrel (w : ℂ) (hw : w ∈ sphere 0 (47/16)) : ‖f w‖ ≤ ‖f 0‖ * Real.exp D := by
    apply (hboundary w hw).trans
    have hn := norm_pos_iff.mpr hf₀
    have h := (Real.log_le_iff_le_exp (div_pos (by linarith) hn)).mp hlog
    simpa only [mul_comm] using (div_le_iff₀ hn).mp h
  have hzZ : z ∉ Z := by
    intro hzZ
    have := hd z hzZ
    simp at this
    linarith
  have hlogder := logDeriv_bound_after_removing_zeros f g Z (analyticOrderNatAt f)
    hroot (fun w _ => hfac w)
    (hg.differentiableOn.diffContOnCl_ball Set.Subset.rfl)
    (fun w hw => hgn w (ball_subset_closedBall hw)) hD hfrel hz hzZ
  have hN : (N : ℝ) ≤ D / Real.log (47/46) :=
    (inner_disk_multiplicity_bound Z hroot hf hf₀ hB hboundary).trans
      (div_le_div_of_nonneg_right hlog (Real.log_nonneg (by norm_num)))
  have hsum : ‖∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (z-ρ)‖ ≤ (N : ℝ) * (1/δ) := by
    apply (norm_sum_le ..).trans
    rw [show (N : ℝ) = ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ) by simp [N], Finset.sum_mul]
    apply Finset.sum_le_sum
    intro ρ hρ
    rw [norm_div, Complex.norm_natCast, mul_one_div]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ (hd ρ hρ)
  have hK : 0 ≤ 1440 * Real.log 48 + 1/δ := by positivity
  calc
    _ ≤ _ := norm_le_norm_sub_add (logDeriv f z) (∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (z-ρ))
    _ ≤ 1440 * (D + (N : ℝ) * Real.log 48) + N * (1/δ) := add_le_add hlogder hsum
    _ = 1440 * D + (N : ℝ) * (1440 * Real.log 48 + 1 / δ) := by ring
    _ ≤ 1440 * D + (D / Real.log (47/46)) * (1440 * Real.log 48 + 1 / δ) := by gcongr
    _ = _ := by ring

end

section

open scoped BigOperators Interval
open ArithmeticFunction

/-- A unit step recovers every von Mangoldt coefficient through the cutoff
with its exact weight. -/
theorem triangularTwist_unit_difference {q : ℕ} (χ : DirichletCharacter ℂ q) (X : ℕ) :
    triangularTwist χ (X+1) - triangularTwist χ X =
      ∑ n ∈ Finset.range (X+1), χ (n : ZMod q) * (vonMangoldt n : ℂ) := by
  unfold triangularTwist
  rw [Finset.sum_range_succ]
  simp only [sub_self, mul_zero, add_zero, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  push_cast
  ring

/-- The difference kernel is bounded by the average of the absolute values
of the complex powers on the intervening unit interval. -/
noncomputable def unitPerronKernel (x : ℝ) (s : ℂ) : ℂ :=
  (((x + 1 : ℝ) : ℂ) ^ (s + 1) - (x : ℂ) ^ (s + 1)) / (s * (s + 1))

theorem unitPerronKernel_norm {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖unitPerronKernel x s‖ ≤ (x + 1) ^ s.re / ‖s‖ := by
  have h := integral_cpow (a := x) (b := x+1) (r := s) (Or.inl (by linarith))
  have he : unitPerronKernel x s = (∫ y : ℝ in x..x+1, (y : ℂ) ^ s) / s := by
    rw [h]
    unfold unitPerronKernel
    rw [div_div, mul_comm s (s+1)]
  have hb : ‖∫ y : ℝ in x..x+1, (y : ℂ) ^ s‖ ≤ (x+1) ^ s.re := by
    calc
      _ ≤ (x+1) ^ s.re * |(x+1)-x| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro y hy
        rw [Set.uIoc_of_le (by linarith)] at hy
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (hx.trans hy.1)]
        exact Real.rpow_le_rpow (hx.trans hy.1).le hy.2 hs
      _ = _ := by simp
  rw [he, norm_div]
  exact div_le_div_of_nonneg_right hb (norm_nonneg _)

/-- When the principal pole is crossed, the unit difference contributes
the midpoint of the two cutoffs. -/
theorem unitPerronKernel_one (x : ℝ) : unitPerronKernel x 1 = (x : ℂ) + 1 / 2 := by
  unfold unitPerronKernel
  norm_num [Complex.cpow_ofNat_mul, show (1+1:ℂ) = (2:ℕ) by norm_num]
  ring

/-- Under the zero-line hypothesis the sum of the residues of the unit
difference kernel has the required square-logarithmic bound. -/
theorem unitPerronKernel_zero_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) {x T : ℝ} (hx : 0 < x) (hT : 2 ≤ T) (Z : Finset ℂ)
    (hGRH : ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 → z.re = 1/2)
    (hZ : ∀ z ∈ Z, 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T ∧ χ.LFunction z = 0) :
    ‖∑ z ∈ Z, (analyticOrderNatAt χ.LFunction z : ℂ) * unitPerronKernel x z‖ ≤
      Real.sqrt (x+1) * ((120 / Real.log (23/22)) * (Real.log (2*q*T))^2) := by
  have H := primitive_reciprocal_zero_sum χ hprim T hT Z hGRH hZ
  calc
    _ ≤ ∑ z ∈ Z, ‖(analyticOrderNatAt χ.LFunction z : ℂ) * unitPerronKernel x z‖ :=
      norm_sum_le _ _
    _ ≤ ∑ z ∈ Z, Real.sqrt (x+1) * ((analyticOrderNatAt χ.LFunction z : ℝ) / ‖z‖) := by
      apply Finset.sum_le_sum
      intro z hz
      obtain ⟨h₀,h₁,_,hL⟩ := hZ z hz
      have h := unitPerronKernel_norm hx h₀.le
      rw [hGRH z h₀ h₁ hL, ← Real.sqrt_eq_rpow] at h
      rw [norm_mul, Complex.norm_natCast]
      calc
        _ ≤ (analyticOrderNatAt χ.LFunction z : ℝ) * (Real.sqrt (x+1) / ‖z‖) :=
          mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
        _ = _ := by ring
    _ = _ := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left H (Real.sqrt_nonneg _)

end

section

open scoped BigOperators

/-- There is a horizontal contour in every unit height interval whose
distance from every nontrivial zero ordinate has an explicit lower bound. -/
theorem primitive_good_height {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (T : ℝ)
    (hGRH : ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 → z.re = 1/2) :
    ∃ t ∈ Set.Icc T (T+1), ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 →
      1 / (3 * ((10 / Real.log (23/22)) * Real.log ((q : ℝ) * (2 + |T + 1/2|)) + 1)) ≤
        |t - z.im| := by
  classical
  let Z := (finite_character_zeros_in_window χ (T+1/2) 1).toFinset
  let B := Z.image Complex.im
  let W := (10 / Real.log (23/22)) * Real.log ((q : ℝ) * (2 + |T+1/2|))
  have hcard : (B.card : ℝ) ≤ W := calc
    _ ≤ (Z.card : ℝ) := by exact_mod_cast Finset.card_image_le
    _ = ∑ _z ∈ Z, (1 : ℝ) := by simp
    _ ≤ ∑ z ∈ Z, (analyticOrderNatAt χ.LFunction z : ℝ) := by
      apply Finset.sum_le_sum
      intro z hz
      obtain ⟨_,h₁,_,hL⟩ := (finite_character_zeros_in_window χ (T+1/2) 1).mem_toFinset.mp hz
      have hne : z ≠ 1 := by intro he; simp [he] at h₁
      exact_mod_cast positive_multiplicity_of_character_zero χ hne hL
    _ ≤ W := primitive_character_full_window_count χ hprim _ hGRH
  obtain ⟨t, ht, hsep⟩ := exists_height_avoiding B T
  refine ⟨t, ht, ?_⟩
  intro z h₀ h₁ hL
  have hc : 0 ≤ (B.card : ℝ) := Nat.cast_nonneg _
  have hmono : 1 / (3 * (W+1)) ≤ 1 / (3 * (B.card+1 : ℝ)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  apply hmono.trans
  by_cases hwin : |z.im - (T+1/2)| ≤ 1
  · apply hsep
    apply Finset.mem_image.mpr
    exact ⟨z,(finite_character_zeros_in_window χ (T+1/2) 1).mem_toFinset.mpr
      ⟨h₀,h₁,hwin,hL⟩,rfl⟩
  · have hhalf : 1 / (3 * (B.card + 1 : ℝ)) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    apply hhalf.trans
    rw [abs_le] at hwin
    rcases lt_or_ge (t-z.im) 0 with h | h
    · rw [abs_of_neg h]
      by_contra! hn
      exact hwin ⟨by linarith [ht.1],by linarith [ht.2]⟩
    · rw [abs_of_nonneg h]
      by_contra! hn
      exact hwin ⟨by linarith [ht.1],by linarith [ht.2]⟩

end

section

open Complex Set Filter MeasureTheory
open scoped BigOperators Topology Interval

/-- Counterclockwise integration over the four directed edges of a rectangle. -/
noncomputable def rectangleBoundary (a b u v : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ x in a..b, f (x + u * I)) - (∫ x in a..b, f (x + v * I)) +
  I * (∫ y in u..v, f (b + y * I)) - I * (∫ y in u..v, f (a + y * I))

private theorem integral_linear_pole_edge (γ : ℝ → ℂ) (V ρ k : ℂ) (a b : ℝ)
    (hγ : ∀ x, HasDerivAt γ V x) (hk : k ≠ 0)
    (hcut : ∀ x ∈ Set.uIcc a b, k * (γ x - ρ) ∈ slitPlane) :
    V * (∫ x in a..b, (γ x - ρ)⁻¹) =
      Complex.log (k * (γ b - ρ)) - Complex.log (k * (γ a - ρ)) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have h := (((hγ x).sub_const ρ).const_mul k).clog_real (hcut x hx)
    simpa only [mul_div_mul_left _ _ hk, div_eq_mul_inv] using h
  · apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.mul
    have hγc : ContinuousOn γ (Set.uIcc a b) := fun x _ => (hγ x).continuousAt.continuousWithinAt
    exact (hγc.sub continuousOn_const).inv₀
      (fun x hx => (mul_ne_zero_iff.mp (slitPlane_ne_zero (hcut x hx))).2)

private theorem log_neg_above {z : ℂ} (hz : 0 < z.im) :
    Complex.log (-z) = Complex.log z - Real.pi * I := by
  simp only [Complex.log, norm_neg, arg_neg_eq_arg_sub_pi_of_im_pos hz, ofReal_sub]
  ring

private theorem log_neg_below {z : ℂ} (hz : z.im < 0) :
    Complex.log (-z) = Complex.log z + Real.pi * I := by
  simp only [Complex.log, norm_neg, arg_neg_eq_arg_add_pi_of_im_neg hz, ofReal_add]
  ring

/-- The logarithmic kernel at any interior point has winding number one. -/
theorem rectangleBoundary_inv_sub (a b u v : ℝ) (ρ : ℂ)
    (ha : a < ρ.re) (hb : ρ.re < b) (hu : u < ρ.im) (hv : ρ.im < v) :
    rectangleBoundary a b u v (fun z => (z - ρ)⁻¹) = 2 * Real.pi * I := by
  let H (y x : ℝ) := (x:ℂ) + (y:ℂ) * I
  let V (x y : ℝ) := (x:ℂ) + (y:ℂ) * I
  have hHd (y x : ℝ) : HasDerivAt (H y) 1 x := by
    simpa [H] using ((hasDerivAt_id x).ofReal_comp.add_const ((y:ℂ) * I))
  have hVd (x y : ℝ) : HasDerivAt (V x) I y := by
    simpa [V] using (((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (x : ℂ))
  have below (x : ℝ) : (H u x - ρ).im < 0 := by simpa [H] using sub_neg.mpr hu
  have above (x : ℝ) : 0 < (H v x - ρ).im := by simpa [H] using sub_pos.mpr hv
  have hbottom := integral_linear_pole_edge (H u) 1 ρ 1 a b (hHd u) one_ne_zero
    (fun x _ => by rw [one_mul]; exact mem_slitPlane_iff.mpr (.inr (below x).ne))
  have htop := integral_linear_pole_edge (H v) 1 ρ 1 a b (hHd v) one_ne_zero
    (fun x _ => by rw [one_mul]; exact mem_slitPlane_iff.mpr (.inr (above x).ne'))
  have hright := integral_linear_pole_edge (V b) I ρ 1 u v (hVd b) one_ne_zero
    (fun y _ => by rw [one_mul]; exact mem_slitPlane_iff.mpr (.inl (by simpa [V] using sub_pos.mpr hb)))
  have hleft := integral_linear_pole_edge (V a) I ρ (-1) u v (hVd a) (by norm_num)
    (fun y _ => by
      rw [neg_one_mul]
      exact mem_slitPlane_iff.mpr (.inl (by simp [V]; linarith)))
  dsimp only [H,V] at *
  simp only [one_mul, neg_one_mul] at hbottom htop hleft hright
  rw [rectangleBoundary, hbottom, htop, hright, hleft,
    log_neg_above (above a), log_neg_below (below a)]
  ring

private theorem rect_principal_edge (a b : ℝ) (γ : ℝ → ℂ) (f G : ℂ → ℂ)
    (P : Finset ℂ) (r : ℂ → ℂ) (hγ : Continuous γ)
    (hG : ContinuousOn (fun x => G (γ x)) (Set.uIcc a b))
    (havoid : ∀ x ∈ Set.uIcc a b, ∀ ρ ∈ P, γ x ≠ ρ)
    (hdecomp : ∀ x ∈ Set.uIcc a b, f (γ x) =
      G (γ x) + ∑ ρ ∈ P, r ρ * (γ x - ρ)⁻¹) :
    (∫ x in a..b, f (γ x)) = (∫ x in a..b, G (γ x)) +
      ∑ ρ ∈ P, r ρ * (∫ x in a..b, (γ x - ρ)⁻¹) := by
  have hi (ρ : ℂ) (hρ : ρ ∈ P) : IntervalIntegrable
      (fun x => r ρ * (γ x - ρ)⁻¹) volume a b :=
    (continuousOn_const.mul ((hγ.continuousOn.sub continuousOn_const).inv₀
      (fun x hx => sub_ne_zero.mpr (havoid x hx ρ hρ)))).intervalIntegrable
  have his : IntervalIntegrable (fun x => ∑ ρ ∈ P, r ρ * (γ x - ρ)⁻¹) volume a b := by
    convert IntervalIntegrable.sum P hi using 1
    ext x
    simp only [Finset.sum_apply]
  rw [intervalIntegral.integral_congr hdecomp,
    intervalIntegral.integral_add hG.intervalIntegrable his,
    intervalIntegral.integral_finsetSum hi]
  simp only [intervalIntegral.integral_const_mul]

/-- The rectangle residue formula, given an analytic regular part after
subtracting the finitely many interior simple principal parts. The pointwise
values assigned to the original function at its poles play no role. -/
theorem rectangle_residues_of_regular_part (a b u v : ℝ) (hab : a ≤ b) (huv : u ≤ v)
    (f G : ℂ → ℂ) (P : Finset ℂ) (r : ℂ → ℂ)
    (hP : ∀ ρ ∈ P, a < ρ.re ∧ ρ.re < b ∧ u < ρ.im ∧ ρ.im < v)
    (hG : DifferentiableOn ℂ G (Set.Icc a b ×ℂ Set.Icc u v))
    (hf : ∀ z ∈ Set.Icc a b ×ℂ Set.Icc u v, z ∉ P →
      f z = G z + ∑ ρ ∈ P, r ρ * (z-ρ)⁻¹) :
    rectangleBoundary a b u v f = (2 * Real.pi * I) * ∑ ρ ∈ P, r ρ := by
  let H (y x : ℝ) := (x:ℂ) + (y:ℂ) * I
  let V (x y : ℝ) := (x:ℂ) + (y:ℂ) * I
  have edge (m n : ℝ) (γ : ℝ → ℂ) (hc : Continuous γ)
      (hγ : ∀ x ∈ Set.uIcc m n, γ x ∈ Set.Icc a b ×ℂ Set.Icc u v)
      (hn : ∀ x ∈ Set.uIcc m n, γ x ∉ P) :
      (∫ x in m..n, f (γ x)) = (∫ x in m..n, G (γ x)) +
        ∑ ρ ∈ P, r ρ * (∫ x in m..n, (γ x - ρ)⁻¹) :=
    rect_principal_edge m n γ f G P r hc (hG.continuousOn.comp hc.continuousOn hγ)
      (fun x hx ρ hρ he => hn x hx (he ▸ hρ)) (fun x hx => hf _ (hγ x hx) (hn x hx))
  have hor (y : ℝ) (hy : y ∈ Set.Icc u v) (hey : y = u ∨ y = v) := edge a b (H y)
    (by dsimp [H]; fun_prop)
    (by intro x hx; rw [Set.uIcc_of_le hab] at hx; simpa [H, Complex.mem_reProdIm] using
          And.intro hx hy)
    (by intro x _ hp; obtain ⟨_,_,hlo,hhi⟩ := hP _ hp
        simp [H] at hlo hhi
        rcases hey with rfl | rfl <;> linarith)
  have ver (x : ℝ) (hx : x ∈ Set.Icc a b) (hex : x = a ∨ x = b) := edge u v (V x)
    (by dsimp [V]; fun_prop)
    (by intro y hy; rw [Set.uIcc_of_le huv] at hy; simpa [V, Complex.mem_reProdIm] using
          And.intro hx hy)
    (by intro y _ hp; obtain ⟨hlo,hhi,_,_⟩ := hP _ hp
        simp [V] at hlo hhi
        rcases hex with rfl | rfl <;> linarith)
  have hreg : rectangleBoundary a b u v G = 0 := by
    simpa only [rectangleBoundary, smul_eq_mul] using
      Complex.integral_boundary_rect_eq_zero_of_differentiableOn G (⟨a,u⟩ : ℂ) (⟨b,v⟩ : ℂ)
        (by simpa only [Set.uIcc_of_le hab, Set.uIcc_of_le huv] using hG)
  calc
    rectangleBoundary a b u v f = rectangleBoundary a b u v G +
        ∑ ρ ∈ P, r ρ * rectangleBoundary a b u v (fun z => (z-ρ)⁻¹) := by
      change (∫ x in a..b, f (H u x)) - (∫ x in a..b, f (H v x)) +
        I * (∫ y in u..v, f (V b y)) - I * (∫ y in u..v, f (V a y)) = _
      rw [hor u ⟨le_rfl,huv⟩ (.inl rfl), hor v ⟨huv,le_rfl⟩ (.inr rfl),
        ver b ⟨hab,le_rfl⟩ (.inr rfl), ver a ⟨le_rfl,hab⟩ (.inl rfl)]
      simp only [H,V,rectangleBoundary,mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib,
        Finset.mul_sum, mul_left_comm (r _) I]
      ring
    _ = _ := by
      rw [hreg, zero_add, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ hρ
      obtain ⟨h1,h2,h3,h4⟩ := hP ρ hρ
      rw [rectangleBoundary_inv_sub a b u v ρ h1 h2 h3 h4, mul_comm]

/-- Residue theorem for finitely many simple poles in a rectangle. Each pole
has a local holomorphic remainder after removal of its simple principal part.
Only differentiability near the other points of the closed rectangle is needed. -/
theorem rectangle_residues_of_local_principal_parts (a b u v : ℝ) (hab : a ≤ b) (huv : u ≤ v)
    (f : ℂ → ℂ) (P : Finset ℂ) (r : ℂ → ℂ)
    (hP : ∀ ρ ∈ P, a < ρ.re ∧ ρ.re < b ∧ u < ρ.im ∧ ρ.im < v)
    (hhol : ∀ z ∈ Set.Icc a b ×ℂ Set.Icc u v, z ∉ P → DifferentiableAt ℂ f z)
    (hlocal : ∀ ρ ∈ P, ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧
      f =ᶠ[𝓝[≠] ρ] fun z => g z + r ρ * (z-ρ)⁻¹) :
    rectangleBoundary a b u v f = (2 * Real.pi * I) * ∑ ρ ∈ P, r ρ := by
  classical
  choose! g hg hprincipal using hlocal
  let term (p z : ℂ) := r p * (z-p)⁻¹
  let G (z : ℂ) := if z ∈ P then g z z - ∑ p ∈ P.erase z, term p z
                    else f z - ∑ p ∈ P, term p z
  have dsum (S : Finset ℂ) (z : ℂ) (hn : z ∉ S) :
      DifferentiableAt ℂ (fun w => ∑ p ∈ S, term p w) z := by
    apply DifferentiableAt.fun_sum
    intro p hp
    have hzp : z-p ≠ 0 := sub_ne_zero.mpr (fun h => hn (h ▸ hp))
    change DifferentiableAt ℂ (fun w : ℂ => r p * (w-p)⁻¹) z
    fun_prop (disch := assumption)
  apply rectangle_residues_of_regular_part a b u v hab huv f G P r hP
  · intro z hz
    by_cases hp : z ∈ P
    · let H (w : ℂ) := g z w - ∑ p ∈ P.erase z, term p w
      have hnear : G =ᶠ[𝓝 z] H := by
        apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE _ (by simp [G,H,hp])
        have havoid : ∀ᶠ w in 𝓝[≠] z, w ∉ P :=
          nhdsNE_le_cofinite z P.finite_toSet.compl_mem_cofinite
        filter_upwards [hprincipal z hp, havoid] with w hfw hw
        simp only [G, H, ite_eq_right hw]
        rw [← Finset.sum_erase_add _ _ hp, hfw]
        dsimp [term]
        ring
      exact (((hg z hp).differentiableAt.sub (dsum (P.erase z) z (by simp))).congr_of_eventuallyEq
        hnear).differentiableWithinAt
    · have hnear : G =ᶠ[𝓝 z] fun w => f w - ∑ p ∈ P, term p w := by
        filter_upwards [P.finite_toSet.isClosed.compl_mem_nhds hp] with w hw
        exact ite_eq_right hw
      exact (((hhol z hz hp).sub (dsum P z hp)).congr_of_eventuallyEq hnear).differentiableWithinAt
  · intro z _ hz
    simp [G, hz, term]

end

section

open Complex Metric Set MeromorphicOn

theorem nonprincipal_strip_logDeriv_of_separation {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ)
    (hs₀ : 1 / 4 ≤ s.re) (hs₁ : s.re ≤ 2) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → χ.LFunction ρ = 0 → δ ≤ ‖s - ρ‖) :
    ‖logDeriv χ.LFunction s‖ ≤
      (1440 + (1440 * Real.log 48 + 1 / δ) / Real.log (47/46)) *
      (9 * Real.log ((q : ℝ) * (2 + |s.im|))) := by
  let c : ℂ := ⟨3, s.im⟩
  let F (w : ℂ) := χ.LFunction (w + c)
  let U : ℝ := (q : ℝ) * (2 + |s.im|)
  let B := 128 * U
  have hq : 1 ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q from q.pos_of_neZero)
  have hU : 2 ≤ U := calc
    (2 : ℝ) ≤ 2 + |s.im| := le_add_of_nonneg_right (abs_nonneg _)
    _ ≤ U := le_mul_of_one_le_left (by positivity) hq
  have hUpos : 0 < U := by linarith
  have hB : 1 ≤ B := by dsimp only [B]; linarith
  have hc : ‖c‖ ≤ 3 + |s.im| := by simpa [c] using Complex.norm_le_abs_re_add_abs_im c
  have hboundary (w : ℂ) (hw : w ∈ sphere 0 (47/16)) : ‖F w‖ ≤ B := by
    have hwN : ‖w‖ = 47 / 16 := by simpa only [mem_sphere, dist_zero_right] using hw
    have hwre := (abs_le.mp ((Complex.abs_re_le_norm w).trans_eq hwN)).1
    have hRe : 1 / 16 ≤ (w + c).re := by simp only [Complex.add_re, c]; linarith
    have hRepos : 0 < (w + c).re := by linarith
    have hnorm : ‖w + c‖ ≤ 4 * (2 + |s.im|) := by
      linarith [norm_add_le w c, abs_nonneg s.im]
    calc
      _ ≤ ‖w+c‖ * ((q : ℝ) + 1) / (w+c).re :=
        nonprincipal_LFunction_norm_le χ hχ (w+c) hRepos
      _ ≤ 32 * (q:ℝ) * ‖w+c‖ := by
        apply (div_le_iff₀ hRepos).mpr
        have h₁ := mul_le_mul_of_nonneg_right hRe (show 0 ≤ 32 * (q : ℝ) * ‖w+c‖ by positivity)
        have h₂ := mul_le_mul_of_nonneg_left hq (norm_nonneg (w+c))
        linarith only [h₁, h₂]
      _ ≤ 32 * (q:ℝ) * (4 * (2+|s.im|)) := by gcongr
      _ = B := by dsimp only [B, U]; ring
  have hlower : 1/2 ≤ ‖F 0‖ := by
    simpa only [F, zero_add] using (half_le_norm_LFunction_of_re_eq_three χ (s := c) rfl)
  have hFpos : 0 < ‖F 0‖ := by linarith
  have hratio : B / ‖F 0‖ ≤ 256 * U := by
    apply (div_le_iff₀ hFpos).mpr
    calc B = 256 * U * (1/2) := by dsimp only [B]; ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hlower (by positivity)
  have hlog : Real.log (B / ‖F 0‖) ≤ 9 * Real.log U := by
    calc
      _ ≤ Real.log (256 * U) := Real.log_le_log (div_pos (by linarith) hFpos) hratio
      _ = 8 * Real.log 2 + Real.log U := by
        rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_mul (by norm_num) hUpos.ne', Real.log_pow]
        norm_num
      _ ≤ _ := by linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hU]
  have hFa : AnalyticOnNhd ℂ F (closedBall 0 (47/16)) := fun w _ =>
    ((χ.differentiable_LFunction hχ).comp (differentiable_id.add_const c)).analyticAt w
  have hz : ‖s-c‖ ≤ 11 / 4 := by
    have heq : s-c = ((s.re - 3 : ℝ) : ℂ) := by apply Complex.ext <;> simp [c]
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hdist (ρ : ℂ) (hρ : ρ ∈ closedBall 0 (23/8)) (hzero : F ρ = 0) :
      δ ≤ ‖s - c - ρ‖ := by
    have hre := (abs_le.mp ((Complex.abs_re_le_norm ρ).trans (mem_closedBall_zero_iff.mp hρ))).1
    have hpos : 0 < (ρ+c).re := by simp only [Complex.add_re, c]; linarith
    have hlt : (ρ+c).re < 1 := by
      by_contra! h
      exact (χ.LFunction_ne_zero_of_one_le_re (.inl hχ) h) hzero
    rw [show s - c - ρ = s - (ρ+c) by ring]
    exact hsep _ hpos hlt hzero
  have hD : 0 < 9 * Real.log U := mul_pos (by norm_num) (Real.log_pos (by linarith))
  have hh := local_logDeriv_bound_of_distance F hFa (norm_pos_iff.mp hFpos)
    hB hD hδ hboundary hlog hz hdist
  have htrans : logDeriv F (s-c) = logDeriv χ.LFunction s := by
    simp only [F, logDeriv_apply, deriv_comp_add_const, sub_add_cancel]
  rwa [htrans] at hh

/-- Under GRH, the entire line of real part one quarter is at distance
at least one quarter from every nontrivial zero. -/
theorem nonprincipal_quarter_line_logDeriv {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ)
    (hGRH : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → χ.LFunction ρ = 0 → ρ.re = 1/2) :
    ‖logDeriv χ.LFunction (⟨1/4,t⟩ : ℂ)‖ ≤
      (1440 + (1440 * Real.log 48 + 4) / Real.log (47/46)) *
      (9 * Real.log ((q : ℝ) * (2 + |t|))) := by
  have hdist (ρ : ℂ) (h₀ : 0 < ρ.re) (h₁ : ρ.re < 1) (hL : χ.LFunction ρ = 0) :
      1/4 ≤ ‖(⟨1/4,t⟩ : ℂ) - ρ‖ := by
    have h := Complex.abs_re_le_norm ((⟨1/4,t⟩ : ℂ) - ρ)
    simpa only [Complex.sub_re, hGRH ρ h₀ h₁ hL,
      show |(1 : ℝ)/4 - 1/2| = 1/4 by norm_num] using h
  simpa only [show (1:ℝ) / (1/4) = 4 by norm_num] using
    nonprincipal_strip_logDeriv_of_separation χ hχ (⟨1/4,t⟩ : ℂ)
      (by norm_num) (by norm_num) (by norm_num : (0:ℝ) < 1/4) hdist

end

section

open Complex Metric Filter MeasureTheory Set
open scoped Topology

/-- Growth of the pole-removed zeta function down to the left edge of the
larger disk used for the logarithmic derivative estimate. -/
theorem zeta_regular_norm_le_sixteenth (s : ℂ) (hs : 1/16 ≤ s.re) :
    ‖riemannZeta₁ s‖ ≤ 17 * (1 + ‖s‖)^2 := by
  have hs' : 0 < s.re := by linarith
  have he : -(s.re+1) < -1 := by linarith
  have hI : ‖∫ t in Ioi (1:ℝ), (((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ) * (t:ℂ)^(-(s+1)))‖ ≤ 16 := by
    calc
      _ ≤ ∫ t in Ioi (1:ℝ), t ^ (-(s.re+1)) := by
        apply norm_integral_le_of_norm_le (integrableOn_Ioi_rpow_of_lt he zero_lt_one)
        filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
        have ht' : 0 < t := zero_lt_one.trans (show 1 < t from ht)
        rw [norm_mul, Complex.norm_of_nonneg (Nat.zero_le_self_sub_floor ht'.le),
          norm_cpow_eq_rpow_re_of_pos ht', neg_re, add_re, one_re]
        exact mul_le_of_le_one_left (Real.rpow_nonneg ht'.le _) (Nat.self_sub_floor_lt_one _).le
      _ ≤ 16 := by
        rw [integral_Ioi_rpow_of_lt he zero_lt_one, Real.one_rpow, show -(s.re+1)+1 = -s.re by ring,
          neg_div_neg_eq, div_le_iff₀ hs']
        linarith
  rw [zeta_pole_removed_eq_floor_integral s hs']
  apply (norm_sub_le ..).trans
  rw [norm_mul, norm_mul]
  have hsub : ‖s - 1‖ ≤ ‖s‖ + 1 := by simpa using norm_sub_le s (1:ℂ)
  calc
    _ ≤ ‖s‖ + (‖s‖ + 1) * ‖s‖ * 16 := by gcongr
    _ ≤ _ := by nlinarith [sq_nonneg ‖s‖, norm_nonneg s]

/-- Away from the zeros and pole this is the exact pole subtraction for ζ'/ζ. -/
theorem zeta_logDeriv_subtract_pole {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    logDeriv riemannZeta s = logDeriv riemannZeta₁ s - (s - 1)⁻¹ := by
  have hs' := sub_ne_zero.mpr hs
  have hreg : riemannZeta₁ s ≠ 0 := by
    intro h
    exact hz (by rw [riemannZeta_eq_inv_sub_mul hs, h, mul_zero])
  rw [logDeriv_apply, logDeriv_apply, deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs,
    riemannZeta_eq_inv_sub_mul hs]
  field_simp
  ring


/-- A uniform bound for the logarithmic derivative of ζ away from its
nontrivial zeros, on the full strip traversed by the rectangle. -/
theorem zeta_logDeriv_of_zero_separation (s : ℂ) (hs₀ : 1/4 ≤ s.re) (hs₁ : s.re ≤ 2)
    (hsne : s ≠ 1) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → riemannZeta ρ = 0 → δ ≤ ‖s - ρ‖) :
    ‖logDeriv riemannZeta s‖ ≤
      (1440 + (1440 * Real.log 48 + 1/δ) / Real.log (47/46)) *
        (11 * Real.log (2 + |s.im|)) + ‖s - 1‖⁻¹ := by
  let c : ℂ := ⟨3, s.im⟩
  let U : ℝ := 2 + |s.im|
  let f (w : ℂ) := riemannZeta₁ (c + w)
  let B : ℝ := 512 * U^2
  have hU : 2 ≤ U := le_add_of_nonneg_right (abs_nonneg _)
  have hUpos : 0 < U := by linarith
  have hB : 1 ≤ B := by dsimp only [B]; nlinarith [sq_nonneg (U-2)]
  have hc : ‖c‖ ≤ 3 + |s.im| := by simpa [c] using Complex.norm_le_abs_re_add_abs_im c
  have hcenter : 1 ≤ ‖f 0‖ := by
    have hfac : 2 ≤ ‖c - 1‖ := by
      have hb := Complex.abs_re_le_norm (c-1)
      norm_num [c] at hb
      exact hb
    have hz : (1/2 : ℝ) ≤ ‖riemannZeta c‖ := by
      simpa only [DirichletCharacter.LFunction_modOne_eq] using
        (half_le_norm_LFunction_of_re_eq_three (1 : DirichletCharacter ℂ 1) (s := c) rfl)
    have hne : c ≠ 1 := by intro h; have := congrArg Complex.re h; norm_num [c] at this
    have hreg : riemannZeta₁ c = (c-1) * riemannZeta c := by
      rw [riemannZeta_eq_inv_sub_mul hne, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hne), one_mul]
    simp only [f, add_zero, hreg, norm_mul]
    calc (1:ℝ) = 2 * (1/2) := by norm_num
         _ ≤ _ := mul_le_mul hfac hz (by norm_num) (norm_nonneg _)
  have hpos := zero_lt_one.trans_le hcenter
  have hbound (w : ℂ) (hw : w ∈ sphere 0 (47/16)) : ‖f w‖ ≤ B := by
    have hwN : ‖w‖ = 47/16 := by simpa [mem_sphere] using hw
    have hrew : - (47 /16) ≤ w.re := by
      have := Complex.abs_re_le_norm w
      rw [hwN] at this
      exact (abs_le.mp this).1
    have hzre : 1/16 ≤ (c+w).re := by simp only [add_re, c]; linarith
    have hn : 1 + ‖c + w‖ ≤ 4 * U := by
      have h := norm_add_le c w
      rw [hwN] at h
      dsimp only [U]
      linarith [abs_nonneg s.im]
    calc
      _ ≤ 17 * (1 + ‖c + w‖)^2 := zeta_regular_norm_le_sixteenth _ hzre
      _ ≤ 17 * (4 * U)^2 := by gcongr
      _ ≤ B := by dsimp only [B]; nlinarith [sq_nonneg U]
  have hlog : Real.log (B / ‖f 0‖) ≤ 11 * Real.log U := by
    calc
      _ ≤ Real.log B := Real.log_le_log (div_pos (by linarith) hpos) (div_le_self (by linarith) hcenter)
      _ = 9 * Real.log 2 + 2 * Real.log U := by
        rw [show B = (2 : ℝ)^9 * U^2 by norm_num [B], Real.log_mul (by norm_num) (pow_ne_zero _ hUpos.ne'),
          Real.log_pow, Real.log_pow]
        norm_num
      _ ≤ _ := by linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hU]
  let z := s - c
  have hz0 : c + z = s := by dsimp [z]; abel
  have hzN : ‖z‖ ≤ 11/4 := by
    have hz' : z = ((s.re - 3 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [z,c]
    rw [hz', Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hloc (w : ℂ) (hw : w ∈ closedBall 0 (23/8)) (hfw : f w = 0) : δ ≤ ‖z - w‖ := by
    have hwN : ‖w‖ ≤ 23/8 := mem_closedBall_zero_iff.mp hw
    have hwb := (abs_le.mp ((Complex.abs_re_le_norm w).trans hwN)).1
    have hre : 0 < (c+w).re := by simp only [c, add_re]; linarith
    have hne : c+w ≠ 1 := by
      intro h
      have : riemannZeta₁ (c+w) = 0 := hfw
      simp [h,riemannZeta₁_one] at this
    have hζ : riemannZeta (c+w) = 0 := by
      rw [riemannZeta_eq_inv_sub_mul hne, show riemannZeta₁ (c+w) = 0 from hfw, mul_zero]
    have hlt : (c+w).re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hζ
    have h := hsep _ hre hlt hζ
    rwa [show s - (c+w) = z - w by dsimp [z]; abel] at h
  have han : AnalyticOnNhd ℂ f (closedBall 0 (47/16)) := by
    intro w _
    exact (differentiable_riemannZeta₁.analyticAt (c+w)).comp (by fun_prop)
  have hL := local_logDeriv_bound_of_distance f han (norm_pos_iff.mp hpos) hB
    (show 0 < 11 * Real.log U from mul_pos (by norm_num) (Real.log_pos (by linarith))) hδ
    hbound hlog hzN hloc
  have heq : logDeriv f z = logDeriv riemannZeta₁ s := by
    simp only [logDeriv_apply, f, deriv_comp_const_add, hz0]
  rw [heq] at hL
  have hζ : riemannZeta s ≠ 0 := by
    intro h
    have hlt : s.re < 1 := lt_of_not_ge fun hle => riemannZeta_ne_zero_of_one_le_re hle h
    have hbad := hsep s (by linarith) hlt h
    simp at hbad
    linarith
  rw [zeta_logDeriv_subtract_pole hsne hζ]
  exact (norm_sub_le ..).trans (by rw [norm_inv]; exact add_le_add hL le_rfl)

/-- On the left vertical edge GRH supplies the fixed horizontal distance
one quarter to all nontrivial zeros. -/
theorem zeta_logDeriv_quarter_line (s : ℂ) (hs : s.re = 1/4)
    (hRH : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → riemannZeta ρ = 0 → ρ.re = 1/2) :
    ‖logDeriv riemannZeta s‖ ≤
      (1440 + (1440 * Real.log 48 + 4) / Real.log (47/46)) *
        (11 * Real.log (2 + |s.im|)) + 4/3 := by
  have hsep (ρ : ℂ) (h₀ : 0 < ρ.re) (h₁ : ρ.re < 1) (hzero : riemannZeta ρ = 0) :
      (1/4 : ℝ) ≤ ‖s-ρ‖ := by
    have hb := Complex.abs_re_le_norm (s-ρ)
    norm_num [Complex.sub_re, hs, hRH ρ h₀ h₁ hzero] at hb
    exact hb
  have hne : s ≠ 1 := by intro h; norm_num [h] at hs
  have hn : (3/4 : ℝ) ≤ ‖s-1‖ := by
    have hb := Complex.abs_re_le_norm (s-1)
    norm_num [Complex.sub_re, hs] at hb
    exact hb
  have hi : ‖s-1‖⁻¹ ≤ 4/3 := by
    have := inv_anti₀ (by norm_num : (0:ℝ)<3/4) hn
    norm_num at this ⊢
    exact this
  have h := zeta_logDeriv_of_zero_separation s hs.ge (by linarith) hne (by norm_num) hsep
  norm_num only [one_div_div, div_one] at h
  linarith only [h, hi]

/-- On a horizontal edge separated from the ordinates of all nontrivial
zeros, the pole contributes at most one when the height has modulus at least one. -/
theorem zeta_logDeriv_horizontal (s : ℂ) (hs₀ : 1/4 ≤ s.re) (hs₁ : s.re ≤ 2)
    (ht : 1 ≤ |s.im|) {δ : ℝ} (hδ : 0 < δ)
    (hheight : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → riemannZeta ρ = 0 → δ ≤ |s.im - ρ.im|) :
    ‖logDeriv riemannZeta s‖ ≤
      (1440 + (1440 * Real.log 48 + 1/δ) / Real.log (47/46)) *
        (11 * Real.log (2 + |s.im|)) + 1 := by
  have hn : 1 ≤ ‖s-1‖ := ht.trans (by simpa using Complex.abs_im_le_norm (s-1))
  have hi : ‖s-1‖⁻¹ ≤ 1 := by simpa using inv_anti₀ zero_lt_one hn
  have hsne : s ≠ 1 := by intro he; norm_num [he] at ht
  have h := zeta_logDeriv_of_zero_separation s hs₀ hs₁ hsne hδ (fun ρ h₀ h₁ hzero =>
    (hheight ρ h₀ h₁ hzero).trans (by simpa only [Complex.sub_im] using Complex.abs_im_le_norm (s-ρ)))
  linarith only [h, hi]

end

section

open Complex MeasureTheory Set Filter
open scoped Interval

private theorem inv_shift_abs_integral {u v : ℝ} (hu : u ≤ 0) (hv : 0 ≤ v) :
    (∫ t : ℝ in u..v, (1 + |t|)⁻¹) = Real.log (1 + |u|) + Real.log (1+v) := by
  have hc : Continuous (fun t : ℝ => (1 + |t|)⁻¹) :=
    (continuous_const.add continuous_abs).inv₀ (fun t => (show 1 + |t| ≠ 0 by positivity))
  have posint (w : ℝ) (hw : 0 ≤ w) :
      (∫ t : ℝ in 0..w, (1 + |t|)⁻¹) = Real.log (1+w) := by
    calc
      _ = ∫ t : ℝ in 0..w, (t+1)⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hw] at ht
        change (1+|t|)⁻¹ = (t+1)⁻¹
        rw [abs_of_nonneg ht.1, add_comm]
      _ = ∫ t : ℝ in (0+1)..(w+1), t⁻¹ := intervalIntegral.integral_comp_add_right _ _
      _ = _ := by rw [integral_inv_of_pos (by norm_num) (by linarith)]; simp [add_comm]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable u 0)
    (hc.intervalIntegrable 0 v), posint _ hv, abs_of_nonpos hu]
  congr 1
  have hn := intervalIntegral.integral_comp_neg (a := 0) (b := -u)
    (fun t : ℝ => (1 + |t|)⁻¹)
  simpa only [abs_neg, neg_neg, neg_zero] using
    (hn.symm.trans (by simpa only [abs_neg] using posint (-u) (by linarith)))

/-- Bound the new vertical edge using the uniform logarithmic-derivative bound
on that edge. The unit difference saves one full power of the cutoff. -/
theorem unit_kernel_left_edge (G : ℂ → ℂ) {x M u v : ℝ} (hx : 0 < x)
    (hu : u ≤ 0) (hv : 0 ≤ v) (hM : 0 ≤ M)
    (hG : ∀ t ∈ Icc u v, ‖G ((1/4 : ℂ) + (t : ℂ) * I)‖ ≤ M) :
    ‖∫ t : ℝ in u..v, G ((1/4 : ℂ) + (t : ℂ) * I) *
      unitPerronKernel x ((1/4 : ℂ) + (t : ℂ) * I)‖ ≤
      (5 * M * (x+1) ^ (1/4 : ℝ)) * (Real.log (1+|u|) + Real.log (1+v)) := by
  let D := 5 * M * (x+1)^(1/4 : ℝ)
  have hc : Continuous (fun t : ℝ => D * (1 + |t|)⁻¹) :=
    continuous_const.mul ((continuous_const.add continuous_abs).inv₀
      (fun t => (show 1 + |t| ≠ 0 by positivity)))
  rw [← inv_shift_abs_integral hu hv, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.norm_integral_le_of_norm_le (hu.trans hv) _ (hc.intervalIntegrable _ _)
  apply Eventually.of_forall
  intro t ht
  let s : ℂ := 1/4 + (t : ℂ) * I
  have hr : s.re = 1/4 := by norm_num [s]
  have hi : s.im = t := by norm_num [s]
  have hσ := Complex.abs_re_le_norm s
  have hτ := Complex.abs_im_le_norm s
  rw [hr] at hσ
  rw [hi] at hτ
  have hden : 1 + |t| ≤ 5 * ‖s‖ := by norm_num at hσ; linarith
  have hp : 0 < ‖s‖ := by norm_num at hσ; linarith
  have h := unitPerronKernel_norm (s := s) hx (by rw [hr]; norm_num)
  rw [hr] at h
  rw [norm_mul]
  apply (mul_le_mul (hG t ⟨ht.1.le,ht.2⟩) h (norm_nonneg _) hM).trans
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc
    _ ≤ (M * ((x+1) ^ (1/4 : ℝ) / ‖s‖)) * (5 * ‖s‖) :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    _ = _ := by dsimp only [D]; field_simp

/-- On the two horizontal edges the first-order kernel bound and the whole
width of the strip suffice. -/
theorem unit_kernel_horizontal_edge (G : ℂ → ℂ) {x M t : ℝ} (hx : 0 < x)
    (ht : t ≠ 0) (hM : 0 ≤ M)
    (hG : ∀ σ ∈ Icc (1/4 : ℝ) 2, ‖G ((σ : ℂ) + (t : ℂ) * I)‖ ≤ M) :
    ‖∫ σ : ℝ in (1/4)..2, G ((σ : ℂ) + (t : ℂ) * I) *
      unitPerronKernel x ((σ : ℂ) + (t : ℂ) * I)‖ ≤ 2 * M * (x+1)^2 / |t| := by
  have hb (σ : ℝ) (hσ : σ ∈ Set.uIoc (1/4 : ℝ) 2) :
      ‖G ((σ : ℂ) + (t : ℂ) * I) * unitPerronKernel x ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        M * ((x+1)^2 / |t|) := by
    rw [uIoc_of_le (by norm_num)] at hσ
    let s : ℂ := (σ : ℂ) + (t : ℂ) * I
    have hr : s.re = σ := by simp [s]
    have hi : s.im = t := by simp [s]
    have hden := Complex.abs_im_le_norm s
    rw [hi] at hden
    have h := unitPerronKernel_norm (s := s) hx (by rw [hr]; linarith [hσ.1])
    rw [hr] at h
    rw [norm_mul]
    refine mul_le_mul (hG σ ⟨hσ.1.le,hσ.2⟩) (h.trans ?_) (norm_nonneg _) hM
    apply div_le_div₀ (by positivity) _ (abs_pos.mpr ht) hden
    calc
      _ ≤ (x+1)^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hσ.2
      _ = _ := by norm_num
  apply (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans
  norm_num
  have hp : 0 ≤ M * ((x+1)^2 / |t|) := by positivity
  calc
    _ ≤ (M * ((x+1)^2 / |t|)) * 2 := mul_le_mul_of_nonneg_left (by norm_num) hp
    _ = _ := by ring

end

section

open Complex Filter Set DirichletCharacter
open scoped Classical Topology

/-- Multiplication by an analytic weight multiplies the simple residue by
the value of the weight at the pole. -/
theorem analytic_weight_principal_part {f w : ℂ → ℂ} {ρ r : ℂ}
    (hw : AnalyticAt ℂ w ρ)
    (hf : ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧
      f =ᶠ[𝓝[≠] ρ] fun z => g z + r * (z-ρ)⁻¹) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G ρ ∧
      (fun z => f z * w z) =ᶠ[𝓝[≠] ρ] fun z => G z + (r * w ρ) * (z-ρ)⁻¹ := by
  obtain ⟨g,hg,he⟩ := hf
  refine ⟨fun z => g z * w z + r * dslope w ρ z, ?_, ?_⟩
  · obtain ⟨p,hp⟩ := hw
    exact (hg.mul hp.analyticAt).add
      (analyticAt_const.mul hp.has_fpower_series_dslope_fslope.analyticAt)
  · filter_upwards [he, self_mem_nhdsWithin] with z hz hne
    have hn : z ≠ ρ := hne
    rw [hz, dslope_of_ne w hn, slope_def_field]
    ring

theorem unitPerronKernel_analyticAt {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (unitPerronKernel x) s := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hs
  have h1 : s + 1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  have hpow {y : ℝ} (hy : 0 < y) : AnalyticAt ℂ (fun z : ℂ => (y : ℂ) ^ (z+1)) s := by
    exact ((show Differentiable ℂ (fun z : ℂ => z+1) by fun_prop).const_cpow
      (.inl (by exact_mod_cast hy.ne'))).analyticAt s
  unfold unitPerronKernel
  exact (hpow (show 0 < x+1 by linarith) |>.sub (hpow hx)).div
    (by fun_prop) (mul_ne_zero h0 h1)

private theorem neg_logDeriv_zero_principal_part {f : ℂ → ℂ} {ρ : ℂ}
    (hf : AnalyticAt ℂ f ρ) (ho : analyticOrderAt f ρ ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧ (fun z => -logDeriv f z) =ᶠ[𝓝[≠] ρ]
      fun z => g z + (-(analyticOrderNatAt f ρ : ℂ)) * (z-ρ)⁻¹ := by
  obtain ⟨g,hg,he⟩ := logDeriv_principal_part hf ho
  refine ⟨fun z => -g z, hg.neg, ?_⟩
  filter_upwards [he] with z hz
  rw [hz, div_eq_mul_inv]
  ring

private theorem neg_logDeriv_principal_character_pole (q : ℕ) [NeZero q] :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 1 ∧
      (fun z => -logDeriv (LFunction (1 : DirichletCharacter ℂ q)) z) =ᶠ[𝓝[≠] (1 : ℂ)]
        fun z => g z + 1 * (z-1)⁻¹ := by
  let F := LFunctionTrivChar₁ q
  have ha : AnalyticAt ℂ F 1 := (differentiable_LFunctionTrivChar₁ q).analyticAt 1
  have hn : F 1 ≠ 0 := LFunctionTrivChar₁_apply_one_ne_zero q
  refine ⟨fun z => -logDeriv F z, (ha.deriv.div ha hn).neg, ?_⟩
  filter_upwards [(ha.continuousAt.eventually_ne hn).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hF hz
  have hz' : z ≠ 1 := hz
  have he : F z = (z-1) * LFunction (1 : DirichletCharacter ℂ q) z :=
    Function.update_of_ne hz' _ _
  have hL : LFunction (1 : DirichletCharacter ℂ q) z ≠ 0 := right_ne_zero_of_mul (he ▸ hF)
  simp only [logDeriv_apply, F, deriv_LFunctionTrivChar₁_apply_of_ne_one q hz', one_mul]
  rw [show LFunctionTrivChar₁ q z = _ from he]
  change _ = -(((z-1) * deriv (LFunction (1 : DirichletCharacter ℂ q)) z +
    LFunction (1 : DirichletCharacter ℂ q) z) / _) + _
  field_simp [sub_ne_zero.mpr hz', hL]
  ring

/-- Exact Perron residue identity throughout a positive-real-part rectangle
straddling the point 1. It covers principal and nonprincipal characters of any modulus.
`Z` consists of the zeros in the closed rectangle away from 1, and all
these zeros are assumed strictly inside the rectangle. -/
theorem character_unitPerron_rectangle {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x a b u v : ℝ} (hx : 0 < x) (ha : 0 < a) (ha1 : a < 1) (hb1 : 1 < b)
    (hu : u < 0) (hv : 0 < v) (Z : Finset ℂ)
    (hZ : ∀ z : ℂ, z ∈ Z ↔ z ∈ Icc a b ×ℂ Icc u v ∧ z ≠ 1 ∧ χ.LFunction z = 0)
    (hint : ∀ z ∈ Z, a < z.re ∧ z.re < b ∧ u < z.im ∧ z.im < v) :
    rectangleBoundary a b u v (fun z => -logDeriv χ.LFunction z * unitPerronKernel x z) =
      (2 * Real.pi * I) * ((if χ = 1 then (x : ℂ) + 1/2 else 0) -
        ∑ z ∈ Z, (analyticOrderNatAt χ.LFunction z : ℂ) * unitPerronKernel x z) := by
  classical
  let P := if χ = 1 then insert (1 : ℂ) Z else Z
  let r (z : ℂ) := if χ = 1 ∧ z = 1 then unitPerronKernel x 1
                    else -(analyticOrderNatAt χ.LFunction z : ℂ) * unitPerronKernel x z
  have memP (z : ℂ) : z ∈ P ↔ (χ = 1 ∧ z = 1) ∨ z ∈ Z := by
    by_cases hχ : χ = 1 <;> simp [P,hχ]
  have hane (z : ℂ) (hz : z ≠ 1 ∨ χ ≠ 1) : AnalyticAt ℂ χ.LFunction z := by
    rcases hz with h | h
    · have han : AnalyticOnNhd ℂ χ.LFunction ({1}ᶜ : Set ℂ) :=
        (show DifferentiableOn ℂ χ.LFunction ({1}ᶜ : Set ℂ) from fun w hw =>
          (differentiableAt_LFunction χ w (.inl hw)).differentiableWithinAt).analyticOnNhd
          isOpen_compl_singleton
      exact han z h
    · exact (differentiable_LFunction h).analyticAt z
  have hrect := rectangle_residues_of_local_principal_parts a b u v
    (ha1.trans hb1).le (hu.trans hv).le (fun z => -logDeriv χ.LFunction z * unitPerronKernel x z) P r
  have hgeom (z : ℂ) (hz : z ∈ P) : a < z.re ∧ z.re < b ∧ u < z.im ∧ z.im < v := by
    rcases (memP z).mp hz with ⟨_,rfl⟩ | h
    · exact ⟨ha1,hb1,hu,hv⟩
    · exact hint z h
  have he := hrect hgeom (by
    intro z hz hn
    have hns : ¬(χ = 1 ∧ z = 1) := fun h => hn ((memP z).2 (.inl h))
    have hne : z ≠ 1 ∨ χ ≠ 1 := by tauto
    have hnL : χ.LFunction z ≠ 0 := by
      intro h
      by_cases h1 : z = 1
      · subst z
        exact LFunction_ne_zero_of_one_le_re χ (.inl (by tauto)) (by simp) h
      · exact hn ((memP z).2 <| .inr <| (hZ z).2 ⟨hz,h1,h⟩)
    have hL := hane z hne
    exact ((hL.deriv.div hL hnL).neg.mul (unitPerronKernel_analyticAt hx (ha.trans_le hz.1.1))).differentiableAt) (by
    intro z hz
    have hw := unitPerronKernel_analyticAt (s := z) hx (ha.trans (hgeom z hz).1)
    rcases (memP z).1 hz with ⟨hχ,rfl⟩ | h
    · subst χ
      simpa [r] using analytic_weight_principal_part hw (neg_logDeriv_principal_character_pole q)
    · obtain ⟨_,h1,hL⟩ := (hZ z).1 h
      have ho : analyticOrderAt χ.LFunction z ≠ ⊤ := by
        intro ho
        have hp := positive_multiplicity_of_character_zero χ h1 hL
        simp [analyticOrderNatAt,ho] at hp
      simpa [r,h1] using analytic_weight_principal_part hw
        (neg_logDeriv_zero_principal_part (hane z (.inl h1)) ho))
  rw [he]
  congr 1
  have hn1 : (1 : ℂ) ∉ Z := by intro h; exact ((hZ 1).1 h).2.1 rfl
  have hsum : ∑ z ∈ Z, r z = - ∑ z ∈ Z, (analyticOrderNatAt χ.LFunction z : ℂ) * unitPerronKernel x z := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun z hz => by simp [r,((hZ z).1 hz).2.1]
  by_cases hχ : χ = 1
  · rw [show P = insert (1 : ℂ) Z from ite_eq_left hχ, Finset.sum_insert hn1, hsum]
    simp [r,hχ,unitPerronKernel_one,sub_eq_add_neg]
  · simp [P,hχ,hsum]

/-- Under GRH, avoiding the zero ordinates on the two horizontal sides suffices.
The finite sum ranges precisely over the nontrivial zeros between those sides. -/
theorem character_unitPerron_rectangle_of_GRH {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x a b u v : ℝ} (hx : 0 < x) (ha : 0 < a) (ha' : a < 1/2) (hb : 1 < b)
    (hu : u < 0) (hv : 0 < v)
    (hGRH : ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 → z.re = 1/2)
    (hsafe : ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 → z.im ≠ u ∧ z.im ≠ v) :
    ∃ Z : Finset ℂ,
      (∀ z : ℂ, z ∈ Z ↔ 0 < z.re ∧ z.re < 1 ∧ u < z.im ∧ z.im < v ∧ χ.LFunction z = 0) ∧
      rectangleBoundary a b u v (fun z => -logDeriv χ.LFunction z * unitPerronKernel x z) =
        (2 * Real.pi * I) * ((if χ = 1 then (x : ℂ) + 1/2 else 0) -
          ∑ z ∈ Z, (analyticOrderNatAt χ.LFunction z : ℂ) * unitPerronKernel x z) := by
  classical
  let K := Icc a b ×ℂ Icc u v
  have hfin := finite_character_zeros_on_compact χ
    (show IsCompact K from isCompact_Icc.reProdIm isCompact_Icc)
  let Z := hfin.toFinset
  have hZ (z : ℂ) : z ∈ Z ↔ z ∈ Icc a b ×ℂ Icc u v ∧ z ≠ 1 ∧ χ.LFunction z = 0 :=
    hfin.mem_toFinset
  have hcrit (z : ℂ) (hz : z ∈ Z) :
      0 < z.re ∧ z.re < 1 ∧ u < z.im ∧ z.im < v ∧ χ.LFunction z = 0 := by
    obtain ⟨hbox, hne, hzero⟩ := (hZ z).1 hz
    have h₀ := ha.trans_le hbox.1.1
    have h₁ : z.re < 1 := lt_of_not_ge fun h =>
      LFunction_ne_zero_of_one_le_re χ (.inr hne) h hzero
    obtain ⟨hs₁,hs₂⟩ := hsafe z h₀ h₁ hzero
    exact ⟨h₀,h₁,lt_of_le_of_ne hbox.2.1 hs₁.symm,lt_of_le_of_ne hbox.2.2 hs₂,hzero⟩
  refine ⟨Z,fun z => ⟨hcrit z, ?_⟩, character_unitPerron_rectangle χ hx ha
    (by linarith) hb hu hv Z hZ ?_⟩
  · rintro ⟨h₀,h₁,hu',hv',hzero⟩
    have hline := hGRH z h₀ h₁ hzero
    have hn : z ≠ 1 := by intro h; simp [h] at h₁
    exact (hZ z).2 ⟨⟨⟨by linarith,by linarith⟩,hu'.le,hv'.le⟩,hn,hzero⟩
  · intro z hz
    obtain ⟨h₀,h₁,hu',hv',hzero⟩ := hcrit z hz
    have hline := hGRH z h₀ h₁ hzero
    exact ⟨by linarith,by linarith,hu',hv'⟩

/-- The normalized contour integral differs from its principal-character
main term by the GRH bound for the sum of the enclosed zeros. -/
theorem primitive_unitPerron_rectangle_error {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) {x a b u v T : ℝ} (hx : 0 < x) (ha : 0 < a)
    (ha' : a < 1/2) (hb : 1 < b) (hu : u < 0) (hv : 0 < v) (hT : 2 ≤ T)
    (huT : -T ≤ u) (hvT : v ≤ T)
    (hGRH : ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 → z.re = 1/2)
    (hsafe : ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 → z.im ≠ u ∧ z.im ≠ v) :
    ‖rectangleBoundary a b u v (fun z => -logDeriv χ.LFunction z * unitPerronKernel x z) /
        (2 * Real.pi * I) - (if χ = 1 then (x : ℂ) + 1/2 else 0)‖ ≤
      Real.sqrt (x+1) * ((120 / Real.log (23/22)) * (Real.log (2*q*T))^2) := by
  obtain ⟨Z,hZ,he⟩ := character_unitPerron_rectangle_of_GRH χ hx ha ha' hb hu hv hGRH hsafe
  have hc : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  rw [he,mul_div_cancel_left₀ _ hc,sub_sub_cancel_left,norm_neg]
  apply unitPerronKernel_zero_sum χ hprim hx hT Z hGRH
  intro z hz
  obtain ⟨h₀,h₁,hlo,hhi,hzero⟩ := (hZ z).1 hz
  exact ⟨h₀,h₁,abs_le.mpr ⟨huT.trans hlo.le,hhi.le.trans hvT⟩,hzero⟩

end

section

private noncomputable def logDerivDiskFactor : ℝ :=
  1440 + (1440 * Real.log 48 + 4) / Real.log (47/46)

/-- An absolute constant valid on both the left and horizontal contour edges. -/
noncomputable def contourLogDerivBound : ℝ :=
  11 * logDerivDiskFactor + 2 / Real.log 2

private theorem logDerivDiskFactor_pos : 0 < logDerivDiskFactor := by
  unfold logDerivDiskFactor
  have : 0 < Real.log (47/46) := Real.log_pos (by norm_num)
  positivity

theorem contourLogDerivBound_pos : 0 < contourLogDerivBound := by
  unfold contourLogDerivBound
  positivity [logDerivDiskFactor_pos]

private theorem contour_log_lower {q : ℕ} [NeZero q] (t : ℝ) :
    Real.log 2 ≤ Real.log ((q : ℝ) * (2 + |t|)) := by
  apply Real.log_le_log (by norm_num)
  have hq : 1 ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q from q.pos_of_neZero)
  exact (le_add_of_nonneg_right (abs_nonneg t)).trans (le_mul_of_one_le_left (by positivity) hq)

private theorem absorb_regularized_bound {L : ℝ} (hL : Real.log 2 ≤ L) :
    logDerivDiskFactor * (11 * L) + 2 ≤ contourLogDerivBound * L := by
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hadd : 2 ≤ (2 / Real.log 2) * L := by
    calc (2:ℝ) = (2 / Real.log 2) * Real.log 2 := (div_mul_cancel₀ _ hpos.ne').symm
         _ ≤ _ := mul_le_mul_of_nonneg_left hL (by positivity)
  dsimp only [contourLogDerivBound]
  linarith only [hadd]

private theorem disk_factor_of_separation {u : ℝ} (hu : 0 ≤ u) :
    1440 + (1440 * Real.log 48 + u) / Real.log (47/46) ≤ logDerivDiskFactor * (1+u) := by
  have hd : 0 < Real.log (47/46) := Real.log_pos (by norm_num)
  have hl : 0 ≤ Real.log 48 := Real.log_nonneg (by norm_num)
  have hbase : 1440 + (1440 * Real.log 48) / Real.log (47/46) ≤ logDerivDiskFactor := by
    unfold logDerivDiskFactor
    gcongr
    linarith
  have hinv : 1 / Real.log (47/46) ≤ logDerivDiskFactor := by
    unfold logDerivDiskFactor
    have : 1 / Real.log (47/46) ≤ (1440 * Real.log 48 + 4) / Real.log (47/46) :=
      div_le_div_of_nonneg_right (by linarith) hd.le
    linarith
  calc
    _ = (1440 + (1440 * Real.log 48) / Real.log (47/46)) +
      (1 / Real.log (47/46)) * u := by ring
    _ ≤ logDerivDiskFactor + logDerivDiskFactor * u := by
      exact add_le_add hbase (mul_le_mul_of_nonneg_right hinv hu)
    _ = _ := by ring

private theorem absorb_horizontal_bound {L u : ℝ} (hL : Real.log 2 ≤ L) (hu : 0 ≤ u) :
    (1440 + (1440 * Real.log 48 + u) / Real.log (47/46)) * (11 * L) + 1 ≤
      contourLogDerivBound * (1+u) * L := by
  have hL0 : 0 ≤ L := (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)).trans hL
  calc
    _ ≤ (logDerivDiskFactor * (1+u)) * (11*L) + 1 := by
      exact add_le_add (mul_le_mul_of_nonneg_right (disk_factor_of_separation hu) (by positivity : 0 ≤ 11*L)) le_rfl
    _ ≤ (logDerivDiskFactor * (11*L) + 2) * (1+u) := by linarith
    _ ≤ (contourLogDerivBound * L) * (1+u) :=
      mul_le_mul_of_nonneg_right (absorb_regularized_bound hL) (by positivity)
    _ = _ := by ring

/-- The left contour estimate, including the primitive principal character. -/
theorem primitive_logDeriv_left {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (s : ℂ) (hs : s.re = 1/4)
    (hGRH : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → χ.LFunction ρ = 0 → ρ.re = 1/2) :
    ‖logDeriv χ.LFunction s‖ ≤ contourLogDerivBound * Real.log ((q : ℝ) * (2 + |s.im|)) := by
  have habs := absorb_regularized_bound (contour_log_lower (q := q) s.im)
  by_cases hχ : χ = 1
  · subst χ
    have hc : (1 : DirichletCharacter ℂ q).conductor = q := hprim
    have hq : q = 1 := by simpa only [DirichletCharacter.conductor_one] using hc.symm
    subst q
    simp only [DirichletCharacter.LFunction_modOne_eq, Nat.cast_one, one_mul] at *
    have h := zeta_logDeriv_quarter_line s hs hGRH
    exact h.trans ((add_le_add le_rfl (by norm_num : (4:ℝ)/3 ≤ 2)).trans habs)
  · have heq : (⟨1/4,s.im⟩ : ℂ) = s := Complex.ext hs.symm rfl
    have h := nonprincipal_quarter_line_logDeriv χ hχ s.im hGRH
    rw [heq] at h
    apply h.trans (le_trans _ habs)
    change logDerivDiskFactor * (9 * _) ≤ logDerivDiskFactor * (11 * _) + 2
    have hl := (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)).trans (contour_log_lower (q:=q) s.im)
    nlinarith [mul_nonneg logDerivDiskFactor_pos.le hl]

/-- At a height separated from every zero ordinate, the logarithmic derivative
is uniformly bounded for every primitive character on the horizontal edge. -/
theorem primitive_logDeriv_horizontal {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (s : ℂ) (hs₀ : 1/4 ≤ s.re) (hs₁ : s.re ≤ 2)
    (ht : 1 ≤ |s.im|) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → χ.LFunction ρ = 0 → δ ≤ |s.im - ρ.im|) :
    ‖logDeriv χ.LFunction s‖ ≤
      contourLogDerivBound * (1 + 1/δ) * Real.log ((q : ℝ) * (2 + |s.im|)) := by
  have habs := absorb_horizontal_bound (contour_log_lower (q := q) s.im) (by positivity : 0 ≤ 1/δ)
  by_cases hχ : χ = 1
  · subst χ
    have hc : (1 : DirichletCharacter ℂ q).conductor = q := hprim
    have hq : q = 1 := by simpa only [DirichletCharacter.conductor_one] using hc.symm
    subst q
    simp only [DirichletCharacter.LFunction_modOne_eq, Nat.cast_one, one_mul] at *
    exact (zeta_logDeriv_horizontal s hs₀ hs₁ ht hδ hsep).trans habs
  · have h := nonprincipal_strip_logDeriv_of_separation χ hχ s hs₀ hs₁ hδ
      (fun ρ h₀ h₁ hL => (hsep ρ h₀ h₁ hL).trans
        (by simpa only [Complex.sub_im] using Complex.abs_im_le_norm (s-ρ)))
    apply h.trans (le_trans _ habs)
    have hp : 0 ≤ 1440 + (1440 * Real.log 48 + 1/δ) / Real.log (47/46) := by
      have : 0 < Real.log (47/46) := Real.log_pos (by norm_num)
      positivity
    have hl := (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)).trans (contour_log_lower (q:=q) s.im)
    nlinarith [mul_nonneg hp hl]

end

section

open Complex MeasureTheory
open scoped Interval

/-- Passing from the normalized rectangular residue identity to the sharp
sum. The vertical integrals use the real height parameter on both sides.
The horizontal bounds are for integration in the real direction. -/
theorem sharp_sum_error_of_rectangle (F : ℂ → ℂ) (principal : Prop) [Decidable principal]
    {x sharp : ℂ} {a b u v S R A B : ℝ}
    (hsharp : sharp = (1 / (2 * Real.pi) : ℝ) •
      ∫ t : ℝ, F ((b : ℂ) + (t : ℂ) * I))
    (hres : ‖rectangleBoundary a b u v F / (2 * Real.pi * I) -
      (if principal then x + 1/2 else 0)‖ ≤ S)
    (htail : ‖(∫ t : ℝ, F ((b : ℂ) + (t : ℂ) * I)) -
      (∫ t : ℝ in u..v, F ((b : ℂ) + (t : ℂ) * I))‖ ≤ R)
    (hleft : ‖∫ t : ℝ in u..v, F ((a : ℂ) + (t : ℂ) * I)‖ ≤ A)
    (hbot : ‖∫ s : ℝ in a..b, F ((s : ℂ) + (u : ℂ) * I)‖ ≤ B)
    (htop : ‖∫ s : ℝ in a..b, F ((s : ℂ) + (v : ℂ) * I)‖ ≤ B) :
    ‖sharp - (if principal then x else 0)‖ ≤ S + R + A + 2*B + 1 := by
  let W := ∫ t : ℝ, F ((b : ℂ) + (t : ℂ) * I)
  let V (s : ℝ) := ∫ t : ℝ in u..v, F ((s : ℂ) + (t : ℂ) * I)
  let H (t : ℝ) := ∫ s : ℝ in a..b, F ((s : ℂ) + (t : ℂ) * I)
  let N := rectangleBoundary a b u v F / (2 * Real.pi * I)
  let m : ℂ := if principal then x+1/2 else 0
  let m₀ : ℂ := if principal then x else 0
  have hrect : rectangleBoundary a b u v F = H u - H v + I * V b - I * V a := rfl
  have hc : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hN : 1 ≤ ‖(2 * Real.pi * I : ℂ)‖ := by
    simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    linarith [Real.pi_gt_three]
  have he : sharp - N = (I * (W - V b) + I * V a - H u + H v) / (2 * Real.pi * I) := by
    rw [hsharp]
    change (1 / (2 * Real.pi) : ℝ) • W - rectangleBoundary a b u v F / _ = _
    rw [hrect,Complex.real_smul]
    push_cast
    field_simp [hc,I_ne_zero]
    ring
  change ‖W - V b‖ ≤ R at htail
  change ‖V a‖ ≤ A at hleft
  change ‖H u‖ ≤ B at hbot
  change ‖H v‖ ≤ B at htop
  have hgap : ‖sharp-N‖ ≤ R + A + 2*B := by
    rw [he,norm_div]
    apply (div_le_self (norm_nonneg _) hN).trans
    have h₁ := norm_add_le (I * (W-V b)) (I * V a)
    have h₂ := norm_sub_le (I * (W-V b) + I * V a) (H u)
    have h₃ := norm_add_le (I * (W-V b) + I * V a - H u) (H v)
    simp only [norm_mul,Complex.norm_I,one_mul] at h₁
    linarith
  have hmid : ‖m - m₀‖ ≤ 1 := by
    by_cases hp : principal <;> norm_num [m,m₀,hp]
  change ‖N-m‖ ≤ S at hres
  change ‖sharp - m₀‖ ≤ _
  have h₁ := norm_add_le (sharp-N) (N-m)
  have h₂ := norm_add_le (sharp-N+(N-m)) (m-m₀)
  rw [show sharp-N+(N-m)+(m-m₀) = sharp-m₀ by abel] at h₂
  linarith

end

section

/-- Choose both horizontal edges of a Perron rectangle, bound the logarithmic
derivative there, and bound it on the entire intervening left edge. -/
theorem primitive_good_contour {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (T : ℝ) (hT : 2 ≤ T)
    (hGRH : ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 → z.re = 1/2) :
    let D := 10 / Real.log (23/22)
    let Y := Real.log ((q : ℝ) * (2 + (T+1)))
    ∃ u ∈ Set.Icc (-T-1) (-T), ∃ v ∈ Set.Icc T (T+1),
      (∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → χ.LFunction ρ = 0 → ρ.im ≠ u ∧ ρ.im ≠ v) ∧
      (∀ s : ℂ, 1/4 ≤ s.re → s.re ≤ 2 → (s.im = u ∨ s.im = v) →
        ‖logDeriv χ.LFunction s‖ ≤ contourLogDerivBound * (1 + 3*(D*Y+1)) * Y) ∧
      (∀ s : ℂ, s.re = 1/4 → s.im ∈ Set.Icc u v →
        ‖logDeriv χ.LFunction s‖ ≤ contourLogDerivBound * Y) := by
  let D := 10 / Real.log (23/22)
  let Y := Real.log ((q : ℝ) * (2 + (T+1)))
  let δ := 1 / (3 * (D*Y+1))
  have hD : 0 < D := div_pos (by norm_num) (Real.log_pos (by norm_num))
  have hq : 1 ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q from q.pos_of_neZero)
  have hY : 0 ≤ Y := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq (by linarith))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hlog (t : ℝ) (ht : |t| ≤ T+1) : Real.log ((q : ℝ) * (2+|t|)) ≤ Y := by
    apply Real.log_le_log (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  have good (a : ℝ) (ha : |a+1/2| ≤ T+1) :
      ∃ t ∈ Set.Icc a (a+1), ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → χ.LFunction ρ = 0 →
        δ ≤ |t-ρ.im| := by
    obtain ⟨t, ht, hsep⟩ := primitive_good_height χ hprim a hGRH
    refine ⟨t, ht, fun ρ h₀ h₁ hL => le_trans ?_ (hsep ρ h₀ h₁ hL)⟩
    have hl : 0 ≤ Real.log ((q : ℝ) * (2 + |a+1/2|)) :=
      Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq (by linarith [abs_nonneg (a+1/2)]))
    change 1 / (3 * (D*Y+1)) ≤ 1 / (3 * (D * Real.log ((q:ℝ)*(2+|a+1/2|)) + 1))
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
    exact hlog _ ha
  obtain ⟨u, hu', hus⟩ := good (-T-1) (by rw [abs_le]; constructor <;> linarith)
  obtain ⟨v, hv, hvs⟩ := good T (by rw [abs_le]; constructor <;> linarith)
  have hu : u ∈ Set.Icc (-T-1) (-T) := by simpa using hu'
  refine ⟨u, hu, v, hv, ?_, ?_, ?_⟩
  · intro ρ h₀ h₁ hL
    have h₁' := hus ρ h₀ h₁ hL
    have h₂' := hvs ρ h₀ h₁ hL
    constructor
    · intro he
      simp [he] at h₁'
      linarith
    · intro he
      simp [he] at h₂'
      linarith
  · intro s hs₀ hs₁ he
    have hb : 1 ≤ |s.im| ∧ |s.im| ≤ T+1 := by
      rcases he with he | he
      · rw [he, abs_of_nonpos (by linarith [hu.2])]
        exact ⟨by linarith [hu.2], by linarith [hu.1]⟩
      · rw [he, abs_of_nonneg (by linarith [hv.1])]
        exact ⟨by linarith [hv.1], hv.2⟩
    have hsep (ρ : ℂ) (h₀ : 0 < ρ.re) (h₁ : ρ.re < 1) (hL : χ.LFunction ρ = 0) :
        δ ≤ |s.im - ρ.im| := by
      rcases he with he | he
      · simpa only [he] using hus ρ h₀ h₁ hL
      · simpa only [he] using hvs ρ h₀ h₁ hL
    have h := primitive_logDeriv_horizontal χ hprim s hs₀ hs₁ hb.1 hδ hsep
    have hdiv : 1 / δ = 3 * (D*Y+1) := by simp [δ]
    rw [hdiv] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hlog _ hb.2) (by positivity [contourLogDerivBound_pos]))
  · intro s hs him
    have hti : |s.im| ≤ T+1 := abs_le.mpr ⟨by linarith [hu.1, him.1], him.2.trans hv.2⟩
    exact (primitive_logDeriv_left χ hprim s hs hGRH).trans
      (mul_le_mul_of_nonneg_left (hlog _ hti) contourLogDerivBound_pos.le)

end


section
open Complex ArithmeticFunction DirichletCharacter MeasureTheory Filter
open scoped BigOperators Topology
noncomputable def negLogL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  -deriv χ.LFunction s / χ.LFunction s

noncomputable def rightLineBound : ℝ :=
  ∑' n : ℕ, ‖LSeries.term (fun k => (vonMangoldt k : ℂ)) 2 n‖

theorem rightLineBound_nonneg : 0 ≤ rightLineBound := tsum_nonneg fun _ => norm_nonneg _

theorem negLogL_bound_right {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : s.re = 2) : ‖negLogL χ s‖ ≤ rightLineBound := by
  have h : 1 < s.re := by linarith
  rw [negLogL, deriv_LFunction_eq_deriv_LSeries χ h, LFunction_eq_LSeries χ h,
    ← LSeries_twist_vonMangoldt_eq χ h]
  apply (norm_tsum_le_tsum_norm (LSeriesSummable_twist_vonMangoldt χ h).norm).trans
  apply Summable.tsum_le_tsum _ (LSeriesSummable_twist_vonMangoldt χ h).norm
    (LSeriesSummable_vonMangoldt (s := 2) (by norm_num)).norm
  intro n
  simp only [LSeries.norm_term_eq, hs, Complex.re_ofNat]
  split_ifs
  · rfl
  · apply div_le_div_of_nonneg_right _ (by positivity)
    change ‖χ (n : ZMod q) * (vonMangoldt n : ℂ)‖ ≤ ‖(vonMangoldt n : ℂ)‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

noncomputable def verticalPoint (σ t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * I

theorem continuous_verticalPoint (σ : ℝ) : Continuous (verticalPoint σ) :=
  continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

set_option maxHeartbeats 1000000 in
theorem negLogL_continuous_right {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Continuous (fun t : ℝ => negLogL χ (verticalPoint 2 t)) := by
  let U := ({1}ᶜ : Set ℂ)
  have ha : AnalyticOnNhd ℂ χ.LFunction U :=
    (show DifferentiableOn ℂ χ.LFunction U from fun w hw =>
      (differentiableAt_LFunction χ w (.inl hw)).differentiableWithinAt).analyticOnNhd
      isOpen_compl_singleton
  apply continuous_iff_continuousAt.mpr
  intro t
  let s := verticalPoint 2 t
  have hre : s.re = 2 := by simp [s, verticalPoint]
  have hs : s ≠ 1 := by intro he; simp [he] at hre
  have hn := LFunction_ne_zero_of_one_le_re χ (s := s) (Or.inr hs) (by linarith)
  have h : AnalyticAt ℂ χ.LFunction s := ha s hs
  have hC : ContinuousAt (fun w => -deriv χ.LFunction w / χ.LFunction w) s :=
    h.deriv.continuousAt.neg.div h.continuousAt hn
  exact ContinuousAt.comp (x := t) hC (continuous_verticalPoint 2).continuousAt


end

end GoldbachDensityProgression

namespace GoldbachDensityTransfer

open Finset ArithmeticFunction Filter
open scoped Topology

def exceptional (n : ℕ) : Prop :=
  4 ≤ n ∧ n % 2 = 0 ∧ ((range (n+1)).filter (fun p => p.Prime ∧ (n-p).Prime)).card = 0

instance (n : ℕ) : Decidable (exceptional n) := by unfold exceptional; infer_instance

def exceptionSet (X : ℕ) := (range (X+1)).filter exceptional

noncomputable def mangoldtConvolution (n : ℕ) : ℝ :=
  ∑ k ∈ range (n+1), vonMangoldt k * vonMangoldt (n-k)

private noncomputable def nonprimePart (k : ℕ) : ℝ :=
  if k.Prime then 0 else vonMangoldt k

private theorem nonprimePart_sum (n : ℕ) :
    ∑ k ∈ range (n+1), nonprimePart k = Chebyshev.psi n - Chebyshev.theta n := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime,Nat.floor_natCast,Finset.sum_filter]
  have hset : range (n+1) = insert 0 (Ioc 0 n) := by
    ext k; simp
  rw [hset,sum_insert (by simp)]
  simp only [nonprimePart,Nat.not_prime_zero,ite_false,ArithmeticFunction.map_zero,zero_add]
  apply sum_congr rfl
  intro k hk
  by_cases h : k.Prime <;> simp [h]

/-- In the absence of a prime representation every nonzero Mangoldt summand
has a proper prime power at one of its endpoints. -/
theorem exceptional_mangoldt_bound {n : ℕ} (hn : exceptional n) :
    mangoldtConvolution n ≤
      2 * (Chebyshev.psi n - Chebyshev.theta n) * Real.log n := by
  have hn' : 1 ≤ n := by unfold exceptional at hn; omega
  have hlog (k : ℕ) (hk : k ≤ n) : vonMangoldt k ≤ Real.log n := by
    rcases eq_or_ne k 0 with rfl | hk₀
    · simpa using Real.log_nonneg (by exact_mod_cast hn')
    exact vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hk₀)
      (by exact_mod_cast hk))
  have hempty := Finset.card_eq_zero.mp hn.2.2
  have hpoint (k : ℕ) (hk : k ∈ range (n+1)) :
      vonMangoldt k * vonMangoldt (n-k) ≤
        nonprimePart k * Real.log n + nonprimePart (n-k) * Real.log n := by
    have hkn := Nat.le_of_lt_succ (mem_range.mp hk)
    have hno : ¬(k.Prime ∧ (n-k).Prime) := by
      intro he
      have hmem : k ∈ (range (n+1)).filter (fun p => p.Prime ∧ (n-p).Prime) := mem_filter.mpr ⟨hk,he⟩
      rw [hempty] at hmem
      exact notMem_empty _ hmem
    by_cases hp : k.Prime
    · have hq : ¬(n-k).Prime := fun h => hno ⟨hp,h⟩
      simp only [nonprimePart,hp,hq,ite_true,ite_false,zero_mul,zero_add]
      rw [mul_comm (vonMangoldt k)]
      exact mul_le_mul_of_nonneg_left (hlog k hkn) vonMangoldt_nonneg
    · have hz : 0 ≤ nonprimePart (n-k) := by unfold nonprimePart; split <;> simp [vonMangoldt_nonneg]
      have hl := Real.log_nonneg (by exact_mod_cast hn' : (1:ℝ) ≤ n)
      rw [nonprimePart,ite_eq_right hp]
      exact (mul_le_mul_of_nonneg_left (hlog (n-k) (Nat.sub_le ..)) vonMangoldt_nonneg).trans
        (le_add_of_nonneg_right (mul_nonneg hz hl))
  have href : (∑ k ∈ range (n+1), nonprimePart (n-k)) = ∑ k ∈ range (n+1), nonprimePart k := by
    simpa using sum_range_reflect nonprimePart (n+1)
  calc
    _ ≤ _ := sum_le_sum hpoint
    _ = _ := by rw [sum_add_distrib,← sum_mul,← sum_mul,href,nonprimePart_sum]; ring

/-- The total Mangoldt convolution on exceptional integers is uniformly
sublinear, so every positive linear main term produces a linear error. -/
theorem exceptional_mangoldt_eventually (c : ℝ) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → exceptional n → mangoldtConvolution n ≤ c * n := by
  obtain ⟨K,hK⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let A := max K 1
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hL := (isLittleO_log_rpow_atTop (r := (1:ℝ)/2) (by norm_num)).bound
    (div_pos hc (mul_pos (by norm_num : (0:ℝ)<2) hA))
  have hNat := tendsto_natCast_atTop_atTop.eventually hL
  obtain ⟨N,hN⟩ := eventually_atTop.mp hNat
  refine ⟨max 1 N,fun n hn he => ?_⟩
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast (le_trans (le_max_left 1 N) hn)
  have hn₀ := zero_le_one.trans hn'
  have hlog := hN n ((le_max_right _ _).trans hn)
  simp only [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hn'),
    ← Real.sqrt_eq_rpow,abs_of_nonneg (Real.sqrt_nonneg _)] at hlog
  have hpow := (hK n).trans (mul_le_mul_of_nonneg_right (le_max_left K 1) (Real.sqrt_nonneg _))
  calc
    _ ≤ _ := exceptional_mangoldt_bound he
    _ ≤ 2*(A*Real.sqrt n)*(c/(2*A)*Real.sqrt n) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpow (by norm_num)) hlog (Real.log_nonneg hn') (by positivity)
    _ = c*n := by
      rw [show 2*(A*Real.sqrt n)*(c/(2*A)*Real.sqrt n) = c*(Real.sqrt n)^2 by field_simp,
        Real.sq_sqrt hn₀]

private theorem fresh_exceptions_bound {X : ℕ} {α A c : ℝ} {D : ℕ → ℝ}
    (hX : 0 < X) (hc : 0 < c)
    (hgap : ∀ n ∈ exceptionSet X \ exceptionSet (X/2), c * X ≤ D n)
    (hmean : ∑ n ∈ range (X+1), (D n)^2 ≤ A*(X:ℝ)^(2+α)) :
    ((exceptionSet X \ exceptionSet (X/2)).card : ℝ) ≤ (A/c^2)*(X:ℝ)^α := by
  let S := exceptionSet X \ exceptionSet (X/2)
  have hXs : 0 < (X:ℝ) := by exact_mod_cast hX
  have hsub : S ⊆ range (X+1) := fun n hn => (mem_filter.mp (mem_sdiff.mp hn).1).1
  have ht : (S.card : ℝ)*(c*X)^2 ≤ ∑ n ∈ range (X+1), (D n)^2 := calc
    _ = ∑ _n ∈ S, (c*X)^2 := by simp
    _ ≤ ∑ n ∈ S, (D n)^2 :=
      sum_le_sum fun n hn => pow_le_pow_left₀ (by positivity) (hgap n hn) _
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => sq_nonneg _
  have hh := ht.trans hmean
  rw [Real.rpow_add hXs,Real.rpow_two] at hh
  change (S.card:ℝ) ≤ _
  rw [div_mul_eq_mul_div,le_div_iff₀ (sq_pos_of_pos hc)]
  apply le_of_mul_le_mul_right _ (sq_pos_of_pos hXs)
  calc
    _ = (S.card:ℝ)*(c*X)^2 := by ring
    _ ≤ _ := hh
    _ = _ := by ring

/-- A power estimate on fresh exceptions in each half-interval gives the same
power for the cumulative count, including the finitely many small inputs. -/
theorem exceptionalCount_of_half_intervals {α K : ℝ} (hα : 0 < α) (N : ℕ)
    (fresh : ∀ X : ℕ, N ≤ X → ((exceptionSet X \ exceptionSet (X/2)).card : ℝ) ≤ K*(X:ℝ)^α) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X → ((exceptionSet X).card : ℝ) ≤ C*(X:ℝ)^α := by
  let B := max 2 N
  let q : ℝ := (1/2:ℝ)^α
  have hq : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  let C := max (B+1:ℝ) (K/(1-q))
  have hC : 0 < C := lt_of_lt_of_le (by positivity : 0 < (B+1:ℝ)) (le_max_left ..)
  have hbudget : C*q+K ≤ C := by
    have hb := (div_le_iff₀ (sub_pos.mpr hq)).mp (show K/(1-q) ≤ C from le_max_right ..)
    linarith
  refine ⟨C,hC,fun X => ?_⟩
  induction X using Nat.strong_induction_on with
  | h X ih =>
    intro hX
    have hXr : (1:ℝ) ≤ X := by exact_mod_cast hX
    have hXp := Real.one_le_rpow hXr hα.le
    by_cases hB : B ≤ X
    · have hB' : max 2 N ≤ X := hB
      have hhalf : 1 ≤ X/2 := by omega
      have hsmall := ih (X/2) (Nat.div_lt_self (by omega) (by norm_num)) hhalf
      have hratio : ((X/2 : ℕ):ℝ)^α ≤ q*(X:ℝ)^α := by
        dsimp [q]; rw [← Real.mul_rpow (by norm_num : (0:ℝ)≤1/2) (Nat.cast_nonneg X)]
        apply Real.rpow_le_rpow (by positivity) _ hα.le
        have hh : X/2*2 ≤ X := Nat.div_mul_le_self ..
        have hh' : ((X/2:ℕ):ℝ)*2 ≤ X := by exact_mod_cast hh
        linarith
      have hfresh := fresh X (by omega)
      have hsub : exceptionSet (X/2) ⊆ exceptionSet X := by
        intro n hn
        obtain ⟨hr,he⟩ := mem_filter.mp hn
        exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hr; omega),he⟩
      have hcard := card_sdiff_add_card_eq_card hsub
      have hh : ((exceptionSet X).card : ℝ) =
          ((exceptionSet X \ exceptionSet (X/2)).card : ℝ) + ((exceptionSet (X/2)).card : ℝ) := by
        exact_mod_cast hcard.symm
      calc
        _ = _ := hh
        _ ≤ K*(X:ℝ)^α+C*(q*(X:ℝ)^α) := add_le_add hfresh (hsmall.trans (mul_le_mul_of_nonneg_left hratio hC.le))
        _ = (C*q+K)*(X:ℝ)^α := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · have hcard := card_le_card (filter_subset exceptional (range (X+1)))
      simp only [card_range] at hcard
      calc
        _ ≤ ((X+1:ℕ):ℝ) := by exact_mod_cast hcard
        _ ≤ (B+1:ℝ) := by push_cast; exact_mod_cast (by omega : X+1 ≤ B+1)
        _ ≤ C := le_max_left ..
        _ ≤ _ := le_mul_of_one_le_right hC.le hXp

private theorem near_info {n X : ℕ} (h : n ∈ exceptionSet X \ exceptionSet (X/2)) :
    X/2 < n ∧ n ≤ X ∧ exceptional n := by
  obtain ⟨hmem,hnout⟩ := mem_sdiff.mp h
  obtain ⟨hr,he⟩ := mem_filter.mp hmem
  refine ⟨?_,Nat.le_of_lt_succ (mem_range.mp hr),he⟩
  by_contra! hlt
  exact hnout (mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hlt),he⟩)

/-- A Hardy–Littlewood mean-square bound for the Mangoldt convolution gives
the same saving of two powers in the genuine prime-pair exceptional count. -/
theorem exceptionalCount_of_mangoldt_mean_square {α c A : ℝ} (hα : 0 < α)
    (hc : 0 < c) (M : ℕ → ℝ) (N : ℕ)
    (hmain : ∀ n, N ≤ n → n % 2 = 0 → c*n ≤ M n)
    (hmean : ∀ X : ℕ, N ≤ X →
      ∑ n ∈ range (X+1), (M n - mangoldtConvolution n)^2 ≤ A*(X:ℝ)^(2+α)) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X → ((exceptionSet X).card : ℝ) ≤ C*(X:ℝ)^α := by
  obtain ⟨N₁,hprime⟩ := exceptional_mangoldt_eventually (c/2) (by positivity)
  apply exceptionalCount_of_half_intervals (K := A/(c/4)^2) hα (2*(max N N₁+2))
  intro X hX
  apply fresh_exceptions_bound (by omega) (by positivity) _ (hmean X (by omega))
  intro n hn
  obtain ⟨hh,_,he⟩ := near_info hn
  have hx2n : X ≤ 2*n := by omega
  have hrel : (X:ℝ) ≤ 2*n := by exact_mod_cast hx2n
  have h₁ := hprime n (by omega) he
  have h₂ := hmain n (by omega) he.2.1
  nlinarith only [h₁,h₂,mul_le_mul_of_nonneg_left hrel hc.le]

/-- The smoothed circle-method version uses a possibly different complex
model at each scale. Its lower bound is needed only for even indices in
the upper half of the range. -/
theorem exceptionalCount_of_smoothed_mean_square {α c A : ℝ} (hα : 0 < α)
    (hc : 0 < c) (V : ℕ → ℕ → ℂ) (N : ℕ)
    (hmain : ∀ X : ℕ, N ≤ X → ∀ n, X/2 < n → n ≤ X → n % 2 = 0 → c*X ≤ ‖V X n‖)
    (hmean : ∀ X : ℕ, N ≤ X →
      ∑ n ∈ range (X+1), ‖((Real.exp (-(n:ℝ)/X) * mangoldtConvolution n : ℝ) : ℂ) - V X n‖^2
        ≤ A*(X:ℝ)^(2+α)) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X → ((exceptionSet X).card : ℝ) ≤ C*(X:ℝ)^α := by
  obtain ⟨N₁,hprime⟩ := exceptional_mangoldt_eventually (c/2) (by positivity)
  apply exceptionalCount_of_half_intervals (K := A/(c/2)^2) hα (2*(max N N₁+2))
  intro X hX
  apply fresh_exceptions_bound (by omega) (by positivity) _ (hmean X (by omega))
  intro n hn
  obtain ⟨hh,hnx,he⟩ := near_info hn
  have hp := hprime n (by omega) he
  have hpos : 0 ≤ mangoldtConvolution n := sum_nonneg fun _ _ =>
    mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg
  have hwt : Real.exp (-(n:ℝ)/X) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr n.cast_nonneg) X.cast_nonneg)
  let z := ((Real.exp (-(n:ℝ)/X) * mangoldtConvolution n : ℝ) : ℂ)
  have hz : ‖z‖ ≤ c/2*X := by
    dsimp only [z]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hpos)]
    exact (mul_le_of_le_one_left hpos hwt).trans (hp.trans
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hnx) (by positivity)))
  have hdiff := norm_sub_norm_le (V X n) z
  rw [norm_sub_rev] at hdiff
  have hM := hmain X (by omega) n hh hnx he.2.1
  change c/2*X ≤ ‖z-V X n‖
  linarith

end GoldbachDensityTransfer

namespace GoldbachDensityCircle

open MeasureTheory Set AddCircle Filter
open scoped Topology

private instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- Bessel's inequality restricted to a finite set of nonnegative frequencies. -/
theorem nat_fourier_bessel (E : Finset ℕ) (f : AddCircle (1:ℝ) → ℂ)
    (hf : MemLp f 2 haarAddCircle) :
    ∑ n ∈ E, ‖fourierCoeff f (n : ℤ)‖^2 ≤ ∫ t, ‖f t‖^2 ∂haarAddCircle := by
  let e : ℕ ↪ ℤ := ⟨Int.ofNat,Int.ofNat_injective⟩
  have H := hasSum_sq_fourierCoeff hf.toLp
  have hcoeff := fourierCoeff_congr_ae hf.coeFn_toLp
  rw [hcoeff] at H
  have hi : (∫ t, ‖(hf.toLp) t‖^2 ∂haarAddCircle) = ∫ t, ‖f t‖^2 ∂haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with t ht
    rw [ht]
  rw [hi] at H
  simpa [e] using (H.summable.sum_le_tsum (E.map e) (fun _ _ => sq_nonneg _)).trans_eq H.tsum_eq

/-- A uniform approximation to an exponential sum bounds the total squared
error in the coefficients of its square. This form permits a discontinuous
major-arc model and an almost-everywhere error bound. -/
theorem finite_coefficient_error (E : Finset ℕ) (F V : AddCircle (1:ℝ) → ℂ)
    (hF : MemLp F 2 haarAddCircle) (hV : MemLp V 2 haarAddCircle)
    {A : ℝ} (herr : ∀ᵐ t ∂haarAddCircle, ‖F t-V t‖ ≤ A) :
    ∑ n ∈ E, ‖fourierCoeff (fun t => (F t)^2) (n : ℤ) -
      fourierCoeff (fun t => (V t)^2) (n : ℤ)‖^2 ≤
      A^2 * ∫ t, ‖F t + V t‖^2 ∂haarAddCircle := by
  let D := fun t => (F t)^2 - (V t)^2
  have hsum : MemLp (fun t => F t+V t) 2 haarAddCircle := hF.add hV
  have hnorm : ∀ᵐ t ∂haarAddCircle, ‖D t‖ ≤ A*‖F t+V t‖ := by
    filter_upwards [herr] with t ht
    change ‖F t ^ 2 - V t ^ 2‖ ≤ _
    rw [sq_sub_sq,norm_mul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right ht (norm_nonneg (F t+V t))
  have hD : MemLp D 2 haarAddCircle := hsum.of_le_mul
    ((hF.aestronglyMeasurable.pow 2).sub (hV.aestronglyMeasurable.pow 2)) hnorm
  have hint (W : AddCircle (1:ℝ) → ℂ) (hW : MemLp W 2 haarAddCircle) :
      Integrable (fun t => W t ^ 2) haarAddCircle := by
    simpa only [pow_two,Pi.mul_apply] using (memLp_one_iff_integrable.mp (hW.fun_mul hW : MemLp (fun t => W t * W t) 1 haarAddCircle))
  have hcoeff (k : ℤ) : fourierCoeff D k =
      fourierCoeff (fun t => (F t)^2) k - fourierCoeff (fun t => (V t)^2) k := by
    simp only [fourierCoeff,D,smul_sub]
    exact integral_sub ((hint F hF).fourier_smul _) ((hint V hV).fourier_smul _)
  simp_rw [← hcoeff]
  apply (nat_fourier_bessel E D hD).trans
  rw [← integral_const_mul]
  apply integral_mono_ae (hD.norm.integrable_sq) (hsum.norm.integrable_sq.const_mul _)
  filter_upwards [hnorm] with t ht
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) ht 2

/-- The smoothed prime or von Mangoldt generating function, in a form
which also admits finitely supported and general absolutely summable weights. -/
noncomputable def positiveFrequencySeries (w : ℕ → ℂ) (t : AddCircle (1:ℝ)) : ℂ :=
  ∑' n : ℕ, w n * fourier (n : ℤ) t

theorem series_continuous {w : ℕ → ℂ} (hw : Summable (fun n => ‖w n‖)) :
    Continuous (positiveFrequencySeries w) := by
  apply continuous_tsum (u := fun n => ‖w n‖) _ hw
  · intro n t
    simp
  · intro n
    exact continuous_const.mul (fourier (n : ℤ)).continuous

theorem series_coefficient {w : ℕ → ℂ} (hw : Summable (fun n => ‖w n‖)) (k : ℤ) :
    fourierCoeff (positiveFrequencySeries w) k =
      ∑' n : ℕ, w n * (Pi.single (n : ℤ) 1 : ℤ → ℂ) k := by
  let G (n : ℕ) (t : AddCircle (1:ℝ)) : ℂ := fourier (-k) t * (w n * fourier (n : ℤ) t)
  have hg (n : ℕ) : Integrable (G n) haarAddCircle :=
    ((fourier (-k)).continuous.mul (continuous_const.mul (fourier (n:ℤ)).continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hgn (n : ℕ) : (∫ t, ‖G n t‖ ∂haarAddCircle) = ‖w n‖ := by
    simp [G]
  have hsw : Summable (fun n => ∫ t, ‖G n t‖ ∂haarAddCircle) := by simpa only [hgn] using hw
  have hmul (t : AddCircle (1:ℝ)) : fourier (-k) t • positiveFrequencySeries w t = ∑' n, G n t := by
    rw [smul_eq_mul, positiveFrequencySeries,← tsum_mul_left]
  rw [fourierCoeff]
  simp_rw [hmul]
  rw [← integral_tsum_of_summable_integral_norm hg hsw]
  apply tsum_congr
  intro n
  change fourierCoeff (fun t : AddCircle (1:ℝ) => w n * fourier (n : ℤ) t) k = _
  rw [fourierCoeff.const_mul, fourierCoeff_fourier]

theorem series_coefficient_nat {w : ℕ → ℂ} (hw : Summable (fun n => ‖w n‖)) (k : ℕ) :
    fourierCoeff (positiveFrequencySeries w) (k : ℤ) = w k := by
  rw [series_coefficient hw]
  rw [tsum_eq_single k]
  · simp
  · intro j hj
    simp [Pi.single_eq_of_ne (show (k:ℤ) ≠ j by exact_mod_cast Ne.symm hj)]

theorem series_coefficient_negative {w : ℕ → ℂ} (hw : Summable (fun n => ‖w n‖))
    {k : ℤ} (hk : k < 0) : fourierCoeff (positiveFrequencySeries w) k = 0 := by
  rw [series_coefficient hw]
  have h (n : ℕ) : w n * (Pi.single (n : ℤ) 1 : ℤ → ℂ) k = 0 := by
    simp [Pi.single_eq_of_ne (show k ≠ (n:ℤ) by omega)]
  simp only [h,tsum_zero]

/-- Parseval for an absolutely convergent one-sided exponential series. -/
theorem series_energy {w : ℕ → ℂ} (hw : Summable (fun n => ‖w n‖)) :
    ∫ t, ‖positiveFrequencySeries w t‖ ^ 2 ∂haarAddCircle = ∑' n : ℕ, ‖w n‖ ^ 2 := by
  let F := positiveFrequencySeries w
  have hf : MemLp F 2 haarAddCircle :=
    (series_continuous hw).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have H := hasSum_sq_fourierCoeff hf.toLp
  rw [fourierCoeff_congr_ae hf.coeFn_toLp] at H
  have hi : (∫ t, ‖(hf.toLp) t‖^2 ∂haarAddCircle) = ∫ t, ‖F t‖^2 ∂haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with t ht
    rw [ht]
  rw [hi] at H
  let c := fun k : ℤ => ‖fourierCoeff F k‖^2
  change HasSum c _ at H
  have hneg (n : ℕ) : c (-(n+1 : ℤ)) = 0 := by
    simp only [c,F,series_coefficient_negative hw (show -(n+1 : ℤ)<0 by omega),norm_zero,zero_pow two_ne_zero]
  have hnegSum : Summable (fun n : ℕ => c (-(n+1 : ℤ))) := by
    simp only [hneg,summable_zero]
  rw [← H.tsum_eq,tsum_of_nat_of_neg_add_one (H.summable.comp_injective Nat.cast_injective) hnegSum]
  simp only [hneg,tsum_zero,add_zero,c,F,series_coefficient_nat hw]

/-- Multiplication of two positive-frequency series gives their ordinary
Cauchy convolution. -/
theorem square_series_coefficient {w : ℕ → ℂ} (hw : Summable (fun n => ‖w n‖)) (k : ℕ) :
    fourierCoeff (fun t => (positiveFrequencySeries w t)^2) (k : ℤ) =
      ∑ j ∈ Finset.range (k+1), w j * w (k-j) := by
  let b := fun n => ∑ j ∈ Finset.range (n+1), w j * w (n-j)
  have hb : Summable (fun n => ‖b n‖) := summable_norm_sum_mul_range_of_summable_norm hw hw
  have hfun : (fun t => (positiveFrequencySeries w t)^2) = positiveFrequencySeries b := by
    funext t
    let a := fun n : ℕ => w n * fourier (n : ℤ) t
    have ha : Summable (fun n => ‖a n‖) := by simpa [a] using hw
    change (∑' n : ℕ, a n)^2 = _
    rw [pow_two, tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm ha ha]
    apply tsum_congr
    intro n
    dsimp only [b,positiveFrequencySeries]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    have H : (j:ℤ) + (↑(n-j):ℤ) = n := by have := Finset.mem_range.mp hj; omega
    rw [← H, fourier_add]
    dsimp only [a]
    ring
  rw [hfun,series_coefficient_nat hb]

noncomputable def mangoldtWeight (X : ℝ) (n : ℕ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt n * Real.exp (-(n:ℝ)/X) : ℝ) : ℂ)

private theorem weight_bound {X : ℝ} (hX : 1 ≤ X) (n : ℕ) :
    ‖mangoldtWeight X n‖ ≤ (Real.log X+2)*Real.exp (-(n:ℝ)/(2*X)) := by
  have hx : 0 < X := by linarith
  have hlog := Real.log_nonneg hX
  have hr : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  rw [mangoldtWeight, Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hr (Real.exp_nonneg _))]
  by_cases hn : n=0
  · subst n; simp; linarith
  have hpos : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  let u := (n:ℝ)/(2*X)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have ha := Real.log_le_sub_one_of_pos (div_pos hpos hx)
  rw [Real.log_div hpos.ne' hx.ne'] at ha
  have hΛ : ArithmeticFunction.vonMangoldt n ≤ Real.log X + 2*u := by
    have eq : 2*u = (n:ℝ)/X := by dsimp [u]; ring
    rw [eq]; linarith [ArithmeticFunction.vonMangoldt_le_log (n:=n)]
  have hau : ArithmeticFunction.vonMangoldt n ≤ (Real.log X+2)*Real.exp u := by
    have hge : 1 ≤ Real.exp u := Real.one_le_exp hu
    nlinarith [Real.add_one_le_exp u,mul_le_mul_of_nonneg_left hge hlog]
  have harg : -(n:ℝ)/X = -u+-u := by dsimp [u]; ring
  rw [harg,Real.exp_add]
  have heq : -(n:ℝ)/(2*X) = -u := by dsimp [u]; ring
  rw [heq]
  calc
    _ ≤ ((Real.log X+2)*Real.exp u) * (Real.exp (-u)*Real.exp (-u)) :=
      mul_le_mul_of_nonneg_right hau (by positivity)
    _ = _ := by rw [Real.exp_neg]; field_simp

private theorem summable_exp_scaled {t : ℝ} (ht : 0<t) :
    Summable (fun n : ℕ => Real.exp (-(n:ℝ)/t)) := by
  simpa only [mul_neg, div_eq_mul_inv, neg_mul] using
    (Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr (inv_pos.mpr ht)))

theorem mangoldtWeight_summable {X : ℝ} (hX : 1 ≤ X) :
    Summable (fun n => ‖mangoldtWeight X n‖) :=
  ((summable_exp_scaled (t:=2*X) (by linarith)).mul_left (Real.log X+2)).of_nonneg_of_le
    (fun n => norm_nonneg _) (weight_bound hX)

theorem mangoldt_series_coefficient {X : ℝ} (hX : 1 ≤ X) (n : ℕ) :
    fourierCoeff (fun t => (positiveFrequencySeries (mangoldtWeight X) t)^2) (n : ℤ) =
      ((Real.exp (-(n:ℝ)/X) * ∑ k ∈ Finset.range (n+1),
        ArithmeticFunction.vonMangoldt k * ArithmeticFunction.vonMangoldt (n-k) : ℝ) : ℂ) := by
  rw [square_series_coefficient (mangoldtWeight_summable hX),Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  have hle : j≤n := by have := Finset.mem_range.mp hj; omega
  have hE : Real.exp (-(j:ℝ)/X)*Real.exp (-(↑(n-j):ℝ)/X) = Real.exp (-(n:ℝ)/X) := by
    rw [← Real.exp_add,Nat.cast_sub hle]
    congr 1
    ring
  unfold mangoldtWeight
  push_cast
  have hc := congrArg Complex.ofReal hE
  push_cast at hc
  rw [← hc]
  ring

theorem mangoldt_series_energy {X : ℝ} (hX : 1 ≤ X) :
    ∫ t, ‖positiveFrequencySeries (mangoldtWeight X) t‖^2 ∂haarAddCircle ≤
      (Real.log X+2)^2 * (X+1) := by
  rw [series_energy (mangoldtWeight_summable hX)]
  let K := (Real.log X+2)^2
  have hx : 0 < X := by linarith
  have hs := (summable_exp_scaled hx).mul_left K
  have hdom (n : ℕ) : ‖mangoldtWeight X n‖^2 ≤ K*Real.exp (-(n:ℝ)/X) := by
    have hw := pow_le_pow_left₀ (norm_nonneg _) (weight_bound hX n) 2
    rw [mul_pow,← Real.exp_nat_mul] at hw
    have he : (↑(2:ℕ):ℝ)*(-(n:ℝ)/(2*X)) = -(n:ℝ)/X := by push_cast; ring
    rwa [he] at hw
  have hs' := hs.of_nonneg_of_le (fun n => sq_nonneg ‖mangoldtWeight X n‖) hdom
  apply (hs'.tsum_le_tsum hdom hs).trans
  rw [tsum_mul_left]
  change _ ≤ K*(X+1)
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  let r := Real.exp (-(1/X))
  have hr : 0 < r := Real.exp_pos _
  have hr' : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (by positivity))
  have ht (n : ℕ) : Real.exp (-(n:ℝ)/X) = r^n := by
    rw [← Real.exp_nat_mul]
    congr 1; ring
  simp_rw [ht]
  rw [tsum_geometric_of_lt_one hr.le hr']
  have E := Real.add_one_le_exp (1/X)
  have hp : 0 < Real.exp (1/X) := Real.exp_pos _
  have hr'' : r ≤ X/(X+1) := by
    rw [show r = (Real.exp (1/X))⁻¹ from Real.exp_neg _]
    rw [← one_div, div_le_div_iff₀ hp (show 0<X+1 by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right E hx.le,div_mul_cancel₀ (1:ℝ) hx.ne']
  apply (inv_le_iff_one_le_mul₀ (sub_pos.mpr hr')).2
  nlinarith [mul_le_mul_of_nonneg_right hr'' (by linarith : 0≤X+1),
    div_mul_cancel₀ X (show X+1 ≠ 0 by linarith)]

end GoldbachDensityCircle

namespace GoldbachDensity

open Complex MeasureTheory Set Filter
open scoped FourierTransform Convolution Topology

private noncomputable def expRay (a : ℝ) : ℝ → ℂ :=
  (Ioi 0).indicator (fun t : ℝ => Complex.exp ((-a:ℂ)*t))

private theorem expRay_integrable {a : ℝ} (ha : 0 < a) : Integrable (expRay a) := by
  apply IntegrableOn.integrable_indicator _ measurableSet_Ioi
  exact integrableOn_exp_mul_complex_Ioi (by simpa using (neg_neg_of_pos ha)) 0

private theorem fourier_expRay {a : ℝ} (ha : 0 < a) (b : ℝ) :
    𝓕 (expRay a) b = 1/((a:ℂ)+2*Real.pi*b*I) := by
  let z : ℂ := -(a:ℂ)-2*Real.pi*b*I
  have hz : z.re < 0 := by simp [z,ha]
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hfun : (fun t : ℝ => Complex.exp ((↑(-2*Real.pi*t*b):ℂ)*I) • expRay a t) =
      (Ioi 0).indicator (fun t : ℝ => Complex.exp (z*t)) := by
    funext t
    by_cases ht : t ∈ Ioi (0:ℝ)
    · simp only [expRay,indicator_of_mem ht,smul_eq_mul,← Complex.exp_add]
      congr 1
      dsimp [z]
      push_cast
      ring
    · simp [expRay,indicator_of_notMem ht]
  rw [hfun,integral_indicator measurableSet_Ioi,integral_exp_mul_complex_Ioi hz]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero]
  dsimp [z]
  rw [show -(a:ℂ)-2*Real.pi*b*I = -((a:ℂ)+2*Real.pi*b*I) by ring, neg_div_neg_eq]

private noncomputable def twiceExpRay (a : ℝ) : ℝ → ℂ :=
  expRay a ⋆[ContinuousLinearMap.mul ℂ ℂ] expRay a

private theorem twiceExpRay_pos (a : ℝ) {y : ℝ} (hy : 0 < y) :
    twiceExpRay a y = y*Complex.exp ((-a:ℂ)*y) := by
  change (∫ t : ℝ, expRay a t * expRay a (y-t)) = _
  have hh : (fun t : ℝ => expRay a t * expRay a (y-t)) =
      (Ioo 0 y).indicator (fun _ : ℝ => Complex.exp ((-a:ℂ)*y)) := by
    funext t
    by_cases h : t ∈ Ioo 0 y
    · have h' : y-t ∈ Ioi (0:ℝ) := sub_pos.mpr h.2
      have ht : t ∈ Ioi (0:ℝ) := h.1
      simp only [expRay,indicator_of_mem ht,indicator_of_mem h',indicator_of_mem h,← Complex.exp_add]
      congr 1; push_cast; ring
    · rw [indicator_of_notMem h]
      by_cases ht : t ∈ Ioi (0:ℝ)
      · have hy' : y-t ∉ Ioi (0:ℝ) := fun hy' => h ⟨ht,sub_pos.mp hy'⟩
        simp [expRay,indicator_of_notMem hy']
      · simp [expRay,indicator_of_notMem ht]
  rw [hh,integral_indicator measurableSet_Ioo,setIntegral_const]
  simp [Measure.real,Real.volume_Ioo,ENNReal.toReal_ofReal hy.le,Algebra.smul_def]

private theorem fourier_twiceExpRay {a : ℝ} (ha : 0 < a) (b : ℝ) :
    𝓕 (twiceExpRay a) b = 1/((a:ℂ)+2*Real.pi*b*I)^2 := by
  rw [twiceExpRay,Real.fourier_mul_convolution_eq (expRay_integrable ha) (expRay_integrable ha),
    fourier_expRay ha]
  simp only [one_div,pow_two,mul_inv_rev]

private theorem normSq_archDen (a b : ℝ) :
    ‖(a:ℂ)+2*Real.pi*b*I‖^2 = a^2 + (2*Real.pi*b)^2 := by
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp
  ring

private theorem fourier_twiceExpRay_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (𝓕 (twiceExpRay a)) := by
  let m := min (a^2) 1
  have hm : 0 < m := lt_min (sq_pos_of_pos ha) zero_lt_one
  have hconst : (2*Real.pi)^2 ≥ (1:ℝ) :=
    one_le_pow₀ (by linarith [Real.pi_gt_three])
  have eqn : 𝓕 (twiceExpRay a) = fun b : ℝ => 1/((a:ℂ)+2*Real.pi*b*I)^2 := funext (fourier_twiceExpRay ha)
  rw [eqn]
  apply ((integrable_inv_one_add_sq).const_mul m⁻¹).mono'
  · exact (by fun_prop : Measurable (fun b : ℝ => 1/((a:ℂ)+2*Real.pi*b*I)^2)).aestronglyMeasurable
  · filter_upwards with b
    rw [norm_div,norm_one,norm_pow,normSq_archDen,one_div,← mul_inv_rev]
    apply inv_anti₀ (by positivity)
    have h₁ := min_le_left (a^2) 1
    have h₂ := (min_le_right (a^2) 1).trans hconst
    dsimp [m] at *
    nlinarith only [h₁,mul_le_mul_of_nonneg_right h₂ (sq_nonneg b)]

/-- The Fourier transform of the squared Laplace denominator gives the exact
archimedean main term in the circle model. -/
theorem archimedean_integral {a y : ℝ} (ha : 0 < a) (hy : 0 < y) :
    (∫ b : ℝ, Complex.exp ((↑(-2*Real.pi*b*y):ℂ)*I) / ((a:ℂ)-2*Real.pi*b*I)^2)
      = y*Complex.exp ((-a:ℂ)*y) := by
  have hi : Integrable (twiceExpRay a) :=
    (expRay_integrable ha).integrable_convolution _ (expRay_integrable ha)
  have hc : ContinuousAt (twiceExpRay a) y := by
    have he : twiceExpRay a =ᶠ[𝓝 y] fun t : ℝ => t*Complex.exp ((-a:ℂ)*t) :=
      (lt_mem_nhds hy).mono (fun _ ht => twiceExpRay_pos a ht)
    exact (by fun_prop : ContinuousAt (fun t : ℝ => t*Complex.exp ((-a:ℂ)*t)) y).congr_of_eventuallyEq he
  have inv := hi.fourier_fourierInv_eq (fourier_twiceExpRay_integrable ha) hc
  rw [twiceExpRay_pos a hy,Real.fourier_real_eq_integral_exp_smul] at inv
  apply Eq.trans _ inv
  apply integral_congr_ae
  filter_upwards with b
  rw [Real.fourierInv_eq_fourier_neg,fourier_twiceExpRay ha,smul_eq_mul,← mul_div_assoc,mul_one]
  congr 2
  push_cast
  ring

private noncomputable def archKernel (a y b : ℝ) : ℂ :=
  Complex.exp ((↑(-2*Real.pi*b*y):ℂ)*I) / ((a:ℂ)-2*Real.pi*b*I)^2

private theorem norm_archKernel (a y b : ℝ) :
    ‖archKernel a y b‖ = 1/(a^2+(2*Real.pi*b)^2) := by
  have hh := normSq_archDen a (-b)
  push_cast at hh
  simp only [mul_neg,neg_mul,← sub_eq_add_neg,neg_sq] at hh
  rw [archKernel,norm_div,Complex.norm_exp,norm_pow,hh]
  simp

private theorem archKernel_integrable {a : ℝ} (ha : 0<a) (y : ℝ) :
    Integrable (archKernel a y) := by
  apply (fourier_twiceExpRay_integrable ha).norm.mono'
  · exact (by unfold archKernel; fun_prop : Measurable (archKernel a y)).aestronglyMeasurable
  · filter_upwards with t
    rw [norm_archKernel,fourier_twiceExpRay ha,norm_div,norm_one,norm_pow,normSq_archDen]

/-- Discarding the two tails outside [-h,h] costs at most 2/h. The estimate
is uniform in the damping parameter and the frequency. -/
theorem truncated_archimedean_error {a y h : ℝ} (ha : 0<a) (hy : 0<y) (hh : 0<h) :
    ‖(∫ b : ℝ in -h..h, Complex.exp ((↑(-2*Real.pi*b*y):ℂ)*I) /
      ((a:ℂ)-2*Real.pi*b*I)^2) - y*Complex.exp ((-a:ℂ)*y)‖ ≤ 2/h := by
  let f := archKernel a y
  have hf : Integrable f := archKernel_integrable ha y
  have hfull : ∫ b, f b = y*Complex.exp ((-a:ℂ)*y) := archimedean_integral ha hy
  change ‖(∫ b in -h..h, f b) - _‖ ≤ _
  rw [intervalIntegral.integral_of_le (by linarith : -h≤h),← hfull,
    ← integral_add_compl measurableSet_Ioc hf,sub_add_cancel_left,norm_neg,
    compl_Ioc,setIntegral_union (Set.disjoint_left.mpr (fun x hx hx' => by
      have hx₁ : x ≤ -h := hx
      have hx₂ : h < x := hx'
      linarith)) measurableSet_Ioi hf.integrableOn hf.integrableOn]
  have hπ : 1 ≤ (2*Real.pi)^2 := one_le_pow₀ (by linarith [Real.pi_gt_three])
  have hmajor (t : ℝ) (ht : 0 < |t|) : ‖f t‖ ≤ 1/t^2 := by
    rw [show ‖f t‖ = 1/(a^2+(2*Real.pi*t)^2) from norm_archKernel a y t]
    apply one_div_le_one_div_of_le (sq_pos_of_ne_zero (abs_pos.mp ht))
    nlinarith only [sq_nonneg a,mul_le_mul_of_nonneg_right hπ (sq_nonneg t)]
  have hI := integrableOn_Ioi_rpow_of_lt (show (-2:ℝ) < -1 by norm_num) hh
  have hmass : (∫ t in Ioi h, t^(-2:ℝ)) = 1/h := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) hh]
    norm_num [Real.rpow_neg hh.le,one_div]
  have hcomp {g : ℝ → ℂ} (hg : Integrable g)
      (hdom : ∀ t ∈ Ioi h, ‖g t‖ ≤ 1/t^2) : ‖∫ t in Ioi h, g t‖ ≤ 1/h := by
    apply (norm_integral_le_integral_norm _).trans
    rw [← hmass]
    apply setIntegral_mono_on hg.norm.integrableOn hI measurableSet_Ioi
    intro t ht
    have hpos : 0<t := hh.trans ht
    simpa only [Real.rpow_neg hpos.le,Real.rpow_two,one_div] using hdom t ht
  have hleft : ‖∫ t in Iic (-h), f t‖ ≤ 1/h := by
    rw [← integral_comp_neg_Ioi]
    apply hcomp hf.comp_neg
    intro t ht
    have hpos : 0<t := hh.trans ht
    simpa [neg_sq] using hmajor (-t) (by simp [abs_of_pos hpos,hpos])
  have hright := hcomp hf (fun t ht => hmajor t (by rw [abs_of_pos (hh.trans ht)]; exact hh.trans ht))
  apply (norm_add_le ..).trans
  exact (add_le_add hleft hright).trans_eq (by ring)

end GoldbachDensity

namespace GoldbachDensity

open Finset Filter
open scoped Topology

/-- The local coefficient in the square of the major-arc model. -/
noncomputable def localTerm (n p : ℕ) : ℝ :=
  if p ∣ n then 1/((p:ℝ)-1) else -1/((p:ℝ)-1)^2

def primesThrough (P : ℕ) : Finset ℕ := (range (P+1)).filter Nat.Prime

private theorem local_factor_ge {p : ℕ} (hp : 2 ≤ p) (n : ℕ) :
    1-1/((p:ℝ)-1)^2 ≤ 1+localTerm n p := by
  have h : 0 < (p:ℝ)-1 := sub_pos.mpr (by exact_mod_cast (by omega : 1 < p))
  by_cases hd : p ∣ n
  · simp only [localTerm,ite_eq_left hd]
    linarith [one_div_pos.mpr h,one_div_pos.mpr (sq_pos_of_pos h)]
  · rw [localTerm,ite_eq_right hd]; apply le_of_eq; ring

/-- The finite singular product has a uniform positive lower bound for every even n.
The comparison factors over *all* integers telescope. -/
theorem singular_product_lower {n : ℕ} (hn : Even n) (P : ℕ) (hP : 2 ≤ P) :
    (P:ℝ)/((P:ℝ)-1) ≤ ∏ p ∈ primesThrough P, (1+localTerm n p) := by
  induction P,hP using Nat.le_induction with
  | base =>
    have he : 2 ∣ n := even_iff_two_dvd.mp hn
    norm_num [primesThrough,Finset.prod_filter,Finset.prod_range_succ,localTerm,he]
  | succ k hk ih =>
    have hk' : 2 ≤ (k:ℝ) := by exact_mod_cast hk
    let b := (1-1/(k:ℝ)^2)
    have hb : 0 ≤ b := by
      dsimp [b]; apply sub_nonneg.mpr
      apply (div_le_one (by positivity : 0 < (k:ℝ)^2)).2
      nlinarith [sq_nonneg ((k:ℝ)-2)]
    rw [primesThrough,Finset.prod_filter,Finset.prod_range_succ]
    have hfactor : b ≤ (if (k+1).Prime then 1+localTerm n (k+1) else 1) := by
      split_ifs
      · simpa [b] using local_factor_ge (p := k+1) (by omega) n
      · exact sub_le_self _ (by positivity)
    rw [primesThrough,Finset.prod_filter] at ih
    have hn₀ : 0 ≤ (k:ℝ)/((k:ℝ)-1) := by apply div_nonneg <;> linarith
    apply le_trans _ (mul_le_mul ih hfactor hb (hn₀.trans ih))
    push_cast
    dsimp [b]
    apply le_of_eq
    rw [add_sub_cancel_right]
    field_simp [show (k:ℝ)-1 ≠ 0 by linarith,show (k:ℝ) ≠ 0 by linarith]
    ring

private theorem sqrt_times_atom_le {n p : ℕ} (hp : p.Prime) (h : ¬ p ∣ n) :
    Real.sqrt p * |localTerm n p| ≤ 4*(p:ℝ)^(-(3/2):ℝ) := by
  have hp₂ : 2 ≤ (p:ℝ) := by exact_mod_cast hp.two_le
  have hp₀ : 0 < (p:ℝ) := by linarith
  have hd : 0 < (p:ℝ)-1 := by linarith
  have he : (p:ℝ)^(-(3/2):ℝ) = Real.sqrt p/(p:ℝ)^2 := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_two,← Real.rpow_sub hp₀]
    norm_num
  rw [he,localTerm,ite_eq_right h,abs_div,abs_neg,abs_one,abs_of_nonneg (sq_nonneg _)]
  rw [mul_one_div,mul_div_assoc']
  apply (div_le_div_iff₀ (sq_pos_of_pos hd) (sq_pos_of_pos hp₀)).2
  have hh : (p:ℝ)^2 ≤ 4*((p:ℝ)-1)^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hp₂) (by linarith : 0 ≤ 3*(p:ℝ)-2)]
  nlinarith only [mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg (p:ℝ))]

private theorem sqrt_times_atom_le_two {n p : ℕ} (hp : p.Prime) (h : p ∣ n) :
    Real.sqrt p * |localTerm n p| ≤ 2 := by
  have hp₂ : 2 ≤ (p:ℝ) := by exact_mod_cast hp.two_le
  have hd : 0 < (p:ℝ)-1 := by linarith
  have hh : Real.sqrt p ≤ (p:ℝ) := (Real.sqrt_le_left (by positivity)).2 (by nlinarith [sq_nonneg ((p:ℝ)-1)])
  rw [localTerm,ite_eq_left h,abs_of_nonneg (one_div_pos.mpr hd).le,mul_one_div]
  apply (div_le_iff₀ hd).2
  linarith

private theorem prime_divisor_product_le {n : ℕ} (hn : 0 < n) (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) {ε : ℝ} (he : 0 < ε) :
    (∏ p ∈ S, if p ∣ n then (p:ℝ)^ε else 1) ≤ (n:ℝ)^ε := by
  let D := S.filter (fun p => p ∣ n)
  have hD : D ⊆ n.primeFactors := by
    intro p hp
    have h := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hS p h.1,h.2,hn.ne'⟩
  rw [← Finset.prod_filter]
  have hprod : ∀ U : Finset ℕ, (∏ p ∈ U, (p:ℝ)^ε) = ((∏ p ∈ U, p : ℕ):ℝ)^ε := by
    intro U
    induction U using Finset.induction_on with
    | empty => simp
    | insert a U ha ih =>
      rw [Finset.prod_insert ha,Finset.prod_insert ha,ih,Nat.cast_mul,Real.mul_rpow (by positivity) (by positivity)]
  rw [hprod]
  apply Real.rpow_le_rpow (by positivity) _ he.le
  exact_mod_cast Nat.le_of_dvd hn ((Finset.prod_dvd_prod_of_subset _ _ id hD).trans (Nat.prod_primeFactors_dvd n))

/-- Rankin's estimate for the absolute local factors, uniform in the prime cutoff. -/
theorem weighted_euler_bound {ε : ℝ} (he : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n P : ℕ), 0 < n →
      (∏ p ∈ primesThrough P, (1+Real.sqrt p*|localTerm n p|)) ≤ C*(n:ℝ)^ε := by
  have htop := (tendsto_rpow_atTop he).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨K,hK⟩ := Filter.eventually_atTop.mp (htop.eventually_ge_atTop 3)
  let f := fun p : ℕ => 4*(p:ℝ)^(-(3/2):ℝ)
  have hf : Summable f := (Real.summable_nat_rpow.mpr (by norm_num : -(3/2:ℝ) < -1)).mul_left 4
  let A := ∑' p, f p
  refine ⟨Real.exp A*3^K,by positivity,?_⟩
  intro n P hn
  let S := primesThrough P
  have hS : ∀ p ∈ S, Nat.Prime p := fun p hp => (Finset.mem_filter.mp hp).2
  let b := fun p : ℕ => if p < K then (3:ℝ) else 1
  let c := fun p : ℕ => if p ∣ n then (p:ℝ)^ε else 1
  have fpos (p : ℕ) : 0 ≤ f p := by dsimp [f]; positivity
  have b₁ (p : ℕ) : 1 ≤ b p := by dsimp [b]; split_ifs <;> norm_num
  have hpbound (p : ℕ) (hp : p ∈ S) :
      1+Real.sqrt p * |localTerm n p| ≤ Real.exp (f p)*b p*c p := by
    have hexp : 1 ≤ Real.exp (f p) := Real.one_le_exp (fpos p)
    by_cases hd : p ∣ n
    · have hp₁ : 1 ≤ (p:ℝ) := by exact_mod_cast (hS p hp).one_le
      have hc : 1 ≤ c p := by simpa [c,hd] using Real.one_le_rpow hp₁ he.le
      have h₃ : 1+Real.sqrt p*|localTerm n p| ≤ 3 := by linarith [sqrt_times_atom_le_two (hS p hp) hd]
      apply h₃.trans
      by_cases hk : p < K
      · dsimp only [b]; rw [ite_eq_left hk]; nlinarith only [hexp,hc,mul_le_mul hexp hc (by norm_num) (Real.exp_pos _).le]
      · have := hK p (le_of_not_gt hk)
        simp only [b,ite_eq_right hk,mul_one,c,ite_eq_left hd] at *
        exact this.trans (le_mul_of_one_le_left (by positivity) hexp)
    · rw [show c p=1 by simp [c,hd],mul_one]
      exact ((add_le_add le_rfl (sqrt_times_atom_le (hS p hp) hd)).trans (by
        linarith only [Real.add_one_le_exp (f p)] : 1+f p ≤ Real.exp (f p))).trans
          (le_mul_of_one_le_right (Real.exp_pos _).le (b₁ p))
  have h₁ : ∏ p ∈ S, Real.exp (f p) ≤ Real.exp A := by
    rw [← Real.exp_sum]
    exact Real.exp_le_exp.mpr (hf.sum_le_tsum S (fun i _ => fpos i))
  have h₂ : ∏ p ∈ S, b p ≤ (3:ℝ)^K := by
    dsimp [b]
    rw [← Finset.prod_filter,Finset.prod_const]
    apply pow_le_pow_right₀ (by norm_num)
    simpa using Finset.card_le_card (show S.filter (fun p => p < K) ⊆ range K from
      fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
  have h₃ := prime_divisor_product_le hn S hS he
  calc
    _ ≤ ∏ p ∈ S, Real.exp (f p)*b p*c p := Finset.prod_le_prod₀ (fun p _ => by positivity) hpbound
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
    _ ≤ (Real.exp A*3^K)*(n:ℝ)^ε := by
      apply mul_le_mul (mul_le_mul h₁ h₂ (Finset.prod_nonneg fun p _ => (b₁ p).trans' zero_le_one)
        (Real.exp_pos _).le) h₃ _ (by positivity)
      apply Finset.prod_nonneg; intro p _; split_ifs <;> positivity

end GoldbachDensity

namespace GoldbachDensity

open Finset Filter
open scoped Topology

def modulusOf (s : Finset ℕ) : ℕ := ∏ p ∈ s, p
noncomputable def localProduct (n : ℕ) (s : Finset ℕ) : ℝ := ∏ p ∈ s, localTerm n p

/-- Truncate by denominator, retaining precisely the squarefree moduli up to P. -/
noncomputable def truncatedSingular (n P : ℕ) : ℝ :=
  ∑ s ∈ (primesThrough P).powerset, if modulusOf s ≤ P then localProduct n s else 0

theorem weighted_singular_sum (n P : ℕ) :
    (∑ s ∈ (primesThrough P).powerset, Real.sqrt (modulusOf s) * |localProduct n s|) =
      ∏ p ∈ primesThrough P, (1+Real.sqrt p*|localTerm n p|) := by
  rw [Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro s hs
  induction s using Finset.induction_on with
  | empty => simp [modulusOf,localProduct]
  | insert a s ha ih =>
    have hs' := Finset.mem_powerset.mp hs
    have hh := ih (Finset.mem_powerset.mpr ((Finset.subset_insert _ _).trans hs'))
    simp only [modulusOf,localProduct,Finset.prod_insert ha,Nat.cast_mul,
      Real.sqrt_mul (Nat.cast_nonneg a),abs_mul] at *
    linear_combination (Real.sqrt a * |localTerm n a|)*hh

/-- The denominator truncation loses at most its Rankin tail. -/
theorem truncated_singular_error {ε : ℝ} (he : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n P : ℕ), 0 < n → 0 < P →
      |(∏ p ∈ primesThrough P, (1+localTerm n p))-truncatedSingular n P|
       ≤ C*(n:ℝ)^ε/Real.sqrt P := by
  obtain ⟨C,hC,hbound⟩ := weighted_euler_bound he
  refine ⟨C,hC,?_⟩
  intro n P hn hp
  have hsp : 0 < Real.sqrt P := Real.sqrt_pos.mpr (by exact_mod_cast hp)
  rw [Finset.prod_one_add,truncatedSingular,← Finset.sum_sub_distrib]
  apply (le_div_iff₀' hsp).2
  apply le_trans (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs ..) hsp.le)
  rw [Finset.mul_sum]
  apply le_trans _ ((weighted_singular_sum n P).le.trans (hbound n P hn))
  apply Finset.sum_le_sum
  intro s _
  change Real.sqrt P * |localProduct n s - (if modulusOf s ≤ P then localProduct n s else 0)| ≤ _
  split_ifs with h
  · simp only [sub_self,abs_zero,mul_zero]; positivity
  · rw [sub_zero]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by exact_mod_cast (not_le.mp h).le)) (abs_nonneg _)

/-- Uniform positivity throughout the range needed by the major-arc model. -/
theorem truncated_singular_positive :
    ∃ P₀ : ℕ, ∀ P : ℕ, P₀ ≤ P → ∀ n : ℕ, 0 < n → n ≤ P^4 → Even n →
      1/2 ≤ truncatedSingular n P := by
  obtain ⟨C,hC,herr⟩ := truncated_singular_error (by norm_num : (0:ℝ)<1/16)
  have htop := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  obtain ⟨K,hK⟩ := eventually_atTop.mp (htop.eventually_ge_atTop (2*C))
  refine ⟨max 2 K,?_⟩
  intro P hP n hn hsize heven
  obtain ⟨hp,hk⟩ := max_le_iff.mp hP
  have hp₀ : 0 < (P:ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hsp := Real.sqrt_pos.mpr hp₀
  have hu : (n:ℝ)^(1/16:ℝ) ≤ (P:ℝ)^(1/4:ℝ) := by
    apply (Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hsize : (n:ℝ) ≤ (P:ℝ)^4) (by norm_num : 0 ≤ (1/16:ℝ))).trans_eq
    rw [← Real.rpow_natCast (P:ℝ) 4,← Real.rpow_mul hp₀.le]
    norm_num
  have hv : (P:ℝ)^(1/4:ℝ)*(P:ℝ)^(1/4:ℝ) = Real.sqrt P := by
    rw [← Real.rpow_add hp₀,Real.sqrt_eq_rpow]; norm_num
  have hB : C*(n:ℝ)^(1/16:ℝ)/Real.sqrt P ≤ 1/2 := by
    apply (div_le_iff₀ hsp).2
    have hh := hK P hk
    change 2*C ≤ (P:ℝ)^(1/4:ℝ) at hh
    nlinarith only [mul_le_mul_of_nonneg_left hu hC.le,
      mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hp₀.le (1/4)),hv]
  have hh := (abs_le.mp ((herr n P hn (by omega)).trans hB)).2
  have hl := singular_product_lower heven P hp
  have hp₂ : 2 ≤ (P:ℝ) := by exact_mod_cast hp
  have hg : 1 ≤ (P:ℝ)/((P:ℝ)-1) := (le_div_iff₀ (by linarith)).2 (by linarith)
  linarith

end GoldbachDensity

namespace GoldbachDensity

open Finset Complex
open scoped ComplexConjugate

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
private theorem char_conjugate_unit (χ : DirichletCharacter ℂ q) (u : (ZMod q)ˣ) :
    conj (χ (u:ZMod q)) = χ (↑u⁻¹ : ZMod q) := by
  have hn : χ (u:ZMod q) ≠ 0 := fun h => by simpa [h] using χ.unit_norm_eq_one u
  apply mul_left_cancel₀ hn
  rw [← map_mul,Units.mul_inv,map_one,Complex.mul_conj,Complex.normSq_eq_norm_sq,χ.unit_norm_eq_one]
  norm_num

/-- Fourier coefficients of a function on the reduced residue classes. -/
noncomputable def charCoefficient (g : (ZMod q)ˣ → ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  (∑ u : (ZMod q)ˣ, g u * conj (χ (u:ZMod q))) / (q.totient:ℂ)

private theorem complex_totient_ne (q : ℕ) [NeZero q] : (q.totient:ℂ) ≠ 0 := by
  exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'

/-- Multiplicative Fourier inversion on units, including q=1. -/
theorem charCoefficient_inversion (g : (ZMod q)ˣ → ℂ) (u : (ZMod q)ˣ) :
    ∑ χ : DirichletCharacter ℂ q, charCoefficient g χ * χ (u:ZMod q) = g u := by
  classical
  simp only [charCoefficient,div_mul_eq_mul_div₀]
  rw [← Finset.sum_div]
  apply (div_eq_iff (complex_totient_ne q)).2
  simp only [Finset.sum_mul,mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,char_conjugate_unit,← ZMod.inv_coe_unit,
    DirichletCharacter.sum_char_inv_mul_char_eq _ (Units.isUnit _) _]
  simp [Units.val_inj,mul_ite]

/-- Parseval's identity, in the normalization used for additive twists. -/
theorem charCoefficient_sq_sum (g : (ZMod q)ˣ → ℂ) (hg : ∀ u, ‖g u‖ = 1) :
    ∑ χ : DirichletCharacter ℂ q, ‖charCoefficient g χ‖^2 = 1 := by
  classical
  have hconj (χ : DirichletCharacter ℂ q) :
      conj (charCoefficient g χ) = (∑ u : (ZMod q)ˣ, conj (g u) * χ (u:ZMod q))/(q.totient:ℂ) := by
    simp [charCoefficient]
  have he : (∑ χ : DirichletCharacter ℂ q, charCoefficient g χ * conj (charCoefficient g χ)) = 1 := by
    simp_rw [hconj,mul_div_assoc',Finset.mul_sum,← mul_assoc,mul_right_comm (charCoefficient g _) (conj _)]
    rw [← Finset.sum_div,Finset.sum_comm]
    simp_rw [← Finset.sum_mul,charCoefficient_inversion,Complex.mul_conj,Complex.normSq_eq_norm_sq,hg]
    simp [ZMod.card_units_eq_totient,complex_totient_ne q]
  exact_mod_cast (by simpa only [Complex.mul_conj,Complex.normSq_eq_norm_sq] using he :
    (∑ χ : DirichletCharacter ℂ q, ((‖charCoefficient g χ‖^2:ℝ):ℂ)) = 1)

/-- The square-root loss in passing from individual characters to a rational
additive twist follows solely from orthogonality. -/
theorem charCoefficient_abs_sum (g : (ZMod q)ˣ → ℂ) (hg : ∀ u, ‖g u‖ = 1) :
    ∑ χ : DirichletCharacter ℂ q, ‖charCoefficient g χ‖ ≤ Real.sqrt q.totient := by
  classical
  have hh := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) (ι := DirichletCharacter ℂ q)
    Finset.univ (fun _ => (1:ℝ)) (fun χ => ‖charCoefficient g χ‖)
  have hc : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card,DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,hc,
    charCoefficient_sq_sum g hg] at hh
  exact (Real.le_sqrt (Finset.sum_nonneg fun _ _ => norm_nonneg _) (Nat.cast_nonneg _)).2 hh

theorem additive_twist_error {g : (ZMod q)ˣ → ℂ} (hg : ∀ u, ‖g u‖ = 1)
    (A : DirichletCharacter ℂ q → ℂ) (M : ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hA : ∀ χ, ‖A χ - (if χ = 1 then M else 0)‖ ≤ B) :
    ‖(∑ χ : DirichletCharacter ℂ q, charCoefficient g χ * A χ) - charCoefficient g 1 * M‖
      ≤ Real.sqrt q.totient * B := by
  classical
  have h : charCoefficient g 1*M = ∑ χ, charCoefficient g χ*(if χ=1 then M else 0) := by
    simp [mul_ite]
  rw [h,← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  apply (norm_sum_le ..).trans
  apply le_trans _ (mul_le_mul_of_nonneg_right (charCoefficient_abs_sum g hg) hB)
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun χ _ => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hA χ) (norm_nonneg _)

end GoldbachDensity

namespace GoldbachDensity

open Complex Real Filter Set MeasureTheory
open scoped ComplexConjugate Topology

theorem gamma_half_norm_sq {s : ℂ} (hs : s.re = 1/2) :
    ‖Complex.Gamma s‖^2 = Real.pi/Real.cosh (Real.pi*s.im) := by
  have hsc : 1-s = conj s := by apply Complex.ext <;> simp [hs]; ring
  have hr : (((Real.pi : ℂ)*s).re) = Real.pi/2 := by simp [hs]; ring
  have hi : (((Real.pi : ℂ)*s).im) = Real.pi*s.im := by simp
  have hsin : Complex.sin ((Real.pi:ℂ)*s) = (Real.cosh (Real.pi*s.im) : ℝ) := by
    rw [Complex.sin_eq, hr,hi]
    simp
  have he := congrArg norm (Complex.Gamma_mul_Gamma_one_sub s)
  rw [hsc,Complex.Gamma_conj,norm_mul,Complex.norm_conj,norm_div,hsin,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg Real.pi_pos.le,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (Real.cosh_pos _)] at he
  simpa only [pow_two] using he

/-- The critical-line Gamma factor has two-sided exponential decay. -/
theorem gamma_half_decay {s : ℂ} (hs : s.re=1/2) :
    ‖Complex.Gamma s‖ ≤ Real.sqrt (2*Real.pi) * Real.exp (-Real.pi*|s.im|/2) := by
  have h := gamma_half_norm_sq hs
  have hc : Real.cosh (Real.pi*s.im) = Real.cosh (Real.pi*|s.im|) := by
    rcases le_total 0 s.im with h|h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h,mul_neg,Real.cosh_neg]
  rw [hc] at h
  have he := Real.exp_pos (-(Real.pi*|s.im|))
  have hcos : Real.exp (Real.pi*|s.im|)/2 ≤ Real.cosh (Real.pi*|s.im|) := by
    rw [Real.cosh_eq]; linarith
  have h2 : ‖Complex.Gamma s‖^2 ≤ 2*Real.pi/Real.exp (Real.pi*|s.im|) := by
    rw [h]
    have hc' := div_le_div_of_nonneg_left Real.pi_pos.le (half_pos (Real.exp_pos _)) hcos
    linarith only [hc',show Real.pi/(Real.exp (Real.pi*|s.im|)/2) =
        2*Real.pi/Real.exp (Real.pi*|s.im|) by ring]
  have hr : (Real.sqrt (2*Real.pi) * Real.exp (-Real.pi*|s.im|/2))^2 =
      2*Real.pi/Real.exp (Real.pi*|s.im|) := by
    rw [mul_pow,Real.sq_sqrt (by positivity),sq,← Real.exp_add,
      show -Real.pi*|s.im|/2 + -Real.pi*|s.im|/2 = -(Real.pi*|s.im|) by ring,
      Real.exp_neg,div_eq_mul_inv]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 (h2.trans_eq hr.symm)

/-- The angular distance to the imaginary axis controls the loss from
complex powers at every point of the open right half-plane. -/
theorem angular_gap_le {z : ℂ} (hz : 0<z.re) :
    z.re/‖z‖ ≤ Real.pi/2 - |z.arg| := by
  have hn : z ≠ 0 := by intro h; simp [h] at hz
  have ha := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  rw [← Complex.cos_arg hn, ← Real.cos_abs, ← Real.sin_pi_div_two_sub]
  exact (Real.sin_lt (by linarith)).le

theorem gamma_half_mellin_decay {s z : ℂ} (hs : s.re=1/2) (hz : 0<z.re) :
    ‖Complex.Gamma s * z^(-s)‖ ≤
      Real.sqrt (2*Real.pi) * ‖z‖^(-(1/2):ℝ) * Real.exp (-(z.re/‖z‖)*|s.im|) := by
  have hn : z ≠ 0 := by intro h; simp [h] at hz
  have ha := angular_gap_le hz
  have ht : z.arg*s.im ≤ |z.arg| * |s.im| := by rw [← abs_mul]; exact le_abs_self _
  have hpow : ‖z^(-s)‖ = ‖z‖^(-(1/2):ℝ)*Real.exp (z.arg*s.im) := by
    rw [Complex.norm_cpow_of_ne_zero hn,Complex.neg_re,Complex.neg_im,hs,mul_neg,
      Real.exp_neg,div_inv_eq_mul]
  rw [norm_mul,hpow]
  apply (mul_le_mul_of_nonneg_right (gamma_half_decay hs) (by positivity)).trans
  calc
    _ = (Real.sqrt (2*Real.pi) * ‖z‖^(-(1/2):ℝ)) *
          Real.exp (-Real.pi*|s.im|/2 + z.arg*s.im) := by rw [Real.exp_add]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      linarith only [ht,mul_le_mul_of_nonneg_right ha (abs_nonneg s.im)]

end GoldbachDensity

namespace GoldbachDensity
open Complex Real Filter Set MeasureTheory
open scoped Topology

/-- Increasing the real part increases the ratio between the absolute complex
Gamma factor and the Gamma factor of its real part, by the beta integral. -/
theorem gamma_norm_shift_le (s : ℂ) (a : ℝ) (hs : 0<s.re) (ha : 0<a) :
    ‖Complex.Gamma s‖ * Real.Gamma (s.re+a) ≤
      Real.Gamma s.re * ‖Complex.Gamma (s+(a:ℂ))‖ := by
  let f (u v : ℂ) (x : ℝ) := (x:ℂ)^(u-1)*(1-(x:ℂ))^(v-1)
  let g (x : ℝ) := x^(s.re-1)*(1-x)^(a-1)
  have hpoint {u : ℂ} (hu : u.re = s.re) {x : ℝ} (hx : 0 < x) (hx' : x < 1) :
      ‖f u a x‖ = g x := by
    unfold f g
    rw [norm_mul,← ofReal_one,← ofReal_sub,Complex.norm_cpow_eq_rpow_re_of_pos hx,
      Complex.norm_cpow_eq_rpow_re_of_pos (sub_pos.mpr hx')]
    simp [hu]
  have hr (x : ℝ) (hx : 0 < x) (hx' : x < 1) : f s.re a x = (g x : ℂ) := by
    unfold f g
    rw [ofReal_mul,ofReal_cpow hx.le,ofReal_cpow (sub_nonneg.mpr hx'.le)]
    push_cast
    rfl
  have hβ : ‖betaIntegral s a‖ ≤ ∫ x : ℝ in (0:ℝ)..1, g x := by
    apply (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0:ℝ)≤1)).trans_eq
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume (1:ℝ)] with x hxn hx
    rw [uIoc_of_le (by norm_num)] at hx
    exact hpoint rfl hx.1 (lt_of_le_of_ne hx.2 hxn)
  have hβ' : betaIntegral (s.re:ℂ) a = ((∫ x : ℝ in (0:ℝ)..1, g x : ℝ):ℂ) := by
    rw [betaIntegral,intervalIntegral.integral_of_le (by norm_num),intervalIntegral.integral_of_le (by norm_num)]
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_ae measurableSet_Ioc
    filter_upwards [Measure.ae_ne volume (1:ℝ)] with x hxn hx
    exact hr x hx.1 (lt_of_le_of_ne hx.2 hxn)
  have hγ := congrArg norm (Complex.Gamma_mul_Gamma_eq_betaIntegral (s:=s) (t:=(a:ℂ)) hs ha)
  rw [norm_mul,norm_mul,Complex.Gamma_ofReal,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.Gamma_pos_of_pos ha)] at hγ
  have hγr := Complex.Gamma_mul_Gamma_eq_betaIntegral (s:=(s.re:ℂ)) (t:=(a:ℂ)) hs ha
  rw [hβ',← ofReal_add,Complex.Gamma_ofReal,Complex.Gamma_ofReal,Complex.Gamma_ofReal,
    ← ofReal_mul,← ofReal_mul,ofReal_inj] at hγr
  have hcomp := mul_le_mul_of_nonneg_left hβ (norm_nonneg (Complex.Gamma (s+(a:ℂ))))
  rw [← hγ] at hcomp
  apply (le_of_mul_le_mul_right _ (Real.Gamma_pos_of_pos ha))
  calc
    _ = (‖Complex.Gamma s‖*Real.Gamma a)*Real.Gamma (s.re+a) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcomp (Real.Gamma_pos_of_pos (add_pos hs ha)).le
    _ = _ := by linear_combination -‖Complex.Gamma (s+(a:ℂ))‖*hγr

theorem gamma_quarter_decay {s : ℂ} (hs : s.re=1/4) :
    ‖Complex.Gamma s‖ ≤ (Real.Gamma (1/4)/Real.Gamma (1/2)*Real.sqrt (2*Real.pi)) *
        Real.exp (-Real.pi*|s.im|/2) := by
  have hp := gamma_norm_shift_le s (1/4) (by rw [hs]; norm_num) (by norm_num)
  rw [hs,show (1/4:ℝ)+1/4 = 1/2 by norm_num] at hp
  have hh := gamma_half_decay (s := s+((1/4:ℝ):ℂ)) (by simp [hs]; norm_num)
  simp only [Complex.add_im,Complex.ofReal_im,add_zero] at hh
  apply (le_div_iff₀ (Real.Gamma_pos_of_pos (by norm_num : 0 < (1/2:ℝ)))).mpr hp |>.trans
  calc
    _ ≤ (Real.Gamma (1/4)*(Real.sqrt (2*Real.pi)*Real.exp (-Real.pi*|s.im|/2)))/Real.Gamma (1/2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh (Real.Gamma_pos_of_pos (by norm_num)).le)
        (Real.Gamma_pos_of_pos (by norm_num)).le
    _ = _ := by ring

theorem gamma_strip_decay :
    ∃ C : ℝ, 0<C ∧ ∀ s : ℂ, 1/4 ≤ s.re → s.re ≤ 2 →
      ‖Complex.Gamma s‖ ≤ C*(3+|s.im|)^2*Real.exp (-Real.pi*|s.im|/2) := by
  obtain ⟨M,hM⟩ := (isCompact_Icc (a:=(1/4:ℝ)) (b:=2)).bddAbove_image (f:=Real.Gamma)
    (show ContinuousOn Real.Gamma (Icc (1/4:ℝ) 2) from fun t ht =>
      (Real.differentiableAt_Gamma (by
        intro n hn
        have := ht.1
        linarith [Nat.cast_nonneg (α:=ℝ) n])).continuousAt.continuousWithinAt)
  have hG : 0 < Real.Gamma (5/2) := Real.Gamma_pos_of_pos (by norm_num)
  have hMpos : 0<M := (Real.Gamma_pos_of_pos (by norm_num : 0<(1:ℝ))).trans_le
    (hM ⟨1,by constructor <;> norm_num,rfl⟩)
  refine ⟨M/Real.Gamma (5/2)*Real.sqrt (2*Real.pi),by positivity,?_⟩
  intro s hlo hhi
  let w : ℂ := ⟨1/2,s.im⟩
  let a := 5/2 - s.re
  have ha : 0<a := by dsimp [a]; linarith
  have he : s+(a:ℂ) = (w+1)+1 := by apply Complex.ext <;> dsimp [a,w] <;> ring
  have hw : w ≠ 0 := by intro hh; have := congrArg Complex.re hh; norm_num [w] at this
  have hw' : w+1 ≠ 0 := by intro hh; have := congrArg Complex.re hh; norm_num [w] at this
  have h₁ := gamma_norm_shift_le s a (by linarith) ha
  rw [show s.re+a = 5/2 by dsimp [a]; ring,he,Complex.Gamma_add_one _ hw',Complex.Gamma_add_one _ hw,
    norm_mul,norm_mul] at h₁
  have h₂ := gamma_half_decay (s:=w) rfl
  have h₃ : ‖w‖ ≤ 3+|s.im| := by
    have h := Complex.norm_le_abs_re_add_abs_im w
    norm_num [w] at h
    linarith
  have h₄ : ‖w+1‖ ≤ 3+|s.im| := by
    apply (norm_add_le w 1).trans
    have h := Complex.norm_le_abs_re_add_abs_im w
    norm_num [w] at h ⊢
    linarith
  have h₅ : Real.Gamma s.re ≤ M := hM ⟨s.re,⟨hlo,hhi⟩,rfl⟩
  apply (le_div_iff₀ hG).mpr h₁ |>.trans
  calc
    _ ≤ M*((3+|s.im|)*((3+|s.im|)*(Real.sqrt (2*Real.pi)*Real.exp (-Real.pi*|s.im|/2)))) /
          Real.Gamma (5/2) := by
      apply div_le_div_of_nonneg_right _ hG.le
      exact mul_le_mul h₅ (mul_le_mul h₄ (mul_le_mul h₃ h₂ (norm_nonneg _) (by positivity))
        (by positivity) (by positivity)) (by positivity) hMpos.le
    _ = _ := by ring

end GoldbachDensity

namespace GoldbachDensity

open Complex Finset Real

/-- Exponential dampening turns local logarithmic counts into a first
moment uniform in the height of the truncation. -/
theorem damped_window_count {Z : Finset ℂ} {w : ℂ → ℝ} {q T A : ℝ}
    (hq : 1 ≤ q) (hT : 1 ≤ T) (hA : 0 ≤ A) (hw : ∀ z ∈ Z, 0 ≤ w z)
    (hcount : ∀ t : ℝ, ∀ S : Finset ℂ,
      (∀ z ∈ S, z ∈ Z ∧ |z.im-t| ≤ 1) →
      (∑ z ∈ S, w z) ≤ A*Real.log (q*(2+|t|))) :
    (∑ z ∈ Z, w z*Real.exp (-|z.im|/T)) ≤
      6*A*(Real.log (q*(2+T))+2)*T := by
  classical
  let L := Real.log (q*(2+T))
  let level := fun z : ℂ => ⌊|z.im|⌋₊
  let shell := fun j => Z.filter (fun z => level z = j)
  have hT₀ : 0 < T := by linarith
  have hq₀ : 0 < q := by linarith
  have hL : 0 ≤ L := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq (by linarith))
  have hloc {j : ℕ} {z : ℂ} (hz : z ∈ shell j) :
      z ∈ Z ∧ (j:ℝ) ≤ |z.im| ∧ |z.im| < (j:ℝ)+1 := by
    obtain ⟨h,hj⟩ := Finset.mem_filter.mp hz
    subst j
    exact ⟨h,Nat.floor_le (abs_nonneg _),Nat.lt_floor_add_one _⟩
  have hc (j : ℕ) : (∑ z ∈ shell j, w z) ≤ 2*A*Real.log (q*(2+(j:ℝ))) := by
    let ℓ := Real.log (q*(2+(j:ℝ)))
    have hb (S : Finset ℂ) (t : ℝ) (ht : |t| = j)
        (hS : ∀ z ∈ S, z ∈ Z ∧ |z.im-t| ≤ 1) : (∑ z ∈ S, w z) ≤ A*ℓ := by
      simpa only [ℓ,ht] using hcount t S hS
    have hp : (∑ z ∈ (shell j).filter (fun z => 0 ≤ z.im), w z) ≤ A*ℓ := by
      apply hb _ j (abs_of_nonneg (Nat.cast_nonneg _))
      intro z hz
      obtain ⟨hs,him⟩ := Finset.mem_filter.mp hz
      obtain ⟨hzZ,hlo,hhi⟩ := hloc hs
      rw [abs_of_nonneg him] at hlo hhi
      exact ⟨hzZ,abs_le.mpr ⟨by linarith, by linarith⟩⟩
    have hn : (∑ z ∈ (shell j).filter (fun z => ¬0 ≤ z.im), w z) ≤ A*ℓ := by
      apply hb _ (-(j:ℝ)) (by simp)
      intro z hz
      obtain ⟨hs,him⟩ := Finset.mem_filter.mp hz
      obtain ⟨hzZ,hlo,hhi⟩ := hloc hs
      rw [abs_of_neg (lt_of_not_ge him)] at hlo hhi
      exact ⟨hzZ,abs_le.mpr ⟨by linarith, by linarith⟩⟩
    rw [← Finset.sum_filter_add_sum_filter_not (shell j) (fun z => 0 ≤ z.im) w]
    change _ ≤ 2*A*ℓ
    linarith only [hp,hn]
  let r := Real.exp (-(1/(2*T)))
  have hr₀ : 0 < r := Real.exp_pos _
  have hr₁ : r < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos (by positivity : 0 < 1/(2*T)))
  have hlog (j : ℕ) : Real.log (q*(2+(j:ℝ))) ≤ L+(j:ℝ)/T := by
    have h :(2+(j:ℝ)) ≤ (2+T)*Real.exp ((j:ℝ)/T) := by
      have he := Real.add_one_le_exp ((j:ℝ)/T)
      apply le_trans _ (mul_le_mul_of_nonneg_left he (by linarith))
      field_simp
      nlinarith only [hT, sq_nonneg T,Nat.cast_nonneg (α := ℝ) j]
    have h' := Real.log_le_log (by positivity : 0 < q*(2+(j:ℝ)))
      (mul_le_mul_of_nonneg_left h hq₀.le)
    rwa [← mul_assoc,Real.log_mul (by positivity) (Real.exp_pos _).ne',Real.log_exp] at h'
  have hratio : (1-r)⁻¹ ≤ 3*T := by
    have he := Real.add_one_le_exp (1/(2*T))
    have hr : r = (Real.exp (1/(2*T)))⁻¹ := Real.exp_neg _
    have hpos : 0 < 1-r := by linarith
    apply (inv_le_comm₀ hpos (by positivity : 0<3*T)).2
    rw [hr]
    apply (le_sub_iff_add_le).2
    have hr' : (Real.exp (1/(2*T)))⁻¹ ≤ (1/(2*T)+1)⁻¹ :=
      inv_anti₀ (by positivity) he
    apply le_trans (add_le_add le_rfl hr') _
    field_simp
    nlinarith only [hT, mul_nonneg (sub_nonneg.mpr hT) hT₀.le]
  have hs (j : ℕ) : (∑ z ∈ shell j, w z*Real.exp (-|z.im|/T)) ≤
      2*A*(L+2)*r^j := by
    have h₁ : (∑ z ∈ shell j, w z*Real.exp (-|z.im|/T)) ≤
        (∑ z ∈ shell j, w z)*Real.exp (-(j:ℝ)/T) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg (hloc hz).2.1) hT₀.le)) (hw z (hloc hz).1)
    have h₂ : (L+(j:ℝ)/T)*Real.exp (-(j:ℝ)/T) ≤ (L+2)*r^j := by
      let u := (j:ℝ)/(2*T)
      have hu : 0 ≤ u := by dsimp [u]; positivity
      have h2u : (j:ℝ)/T = 2*u := by dsimp [u]; ring
      have hrj : r^j = Real.exp (-u) := by
        dsimp [r,u]; rw [← Real.exp_nat_mul]; congr 1; ring
      rw [hrj,neg_div,h2u,show -(2*u) = -u + -u by ring,Real.exp_add,← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      rw [Real.exp_neg,← div_eq_mul_inv]
      apply (div_le_iff₀ (Real.exp_pos _)).2
      have he := Real.add_one_le_exp u
      nlinarith only [mul_nonneg hL (show 0 ≤ Real.exp u - 1 by linarith),he]
    calc
      _ ≤ _ := h₁
      _ ≤ (2*A*(L+(j:ℝ)/T))*Real.exp (-(j:ℝ)/T) :=
        mul_le_mul_of_nonneg_right ((hc j).trans (mul_le_mul_of_nonneg_left (hlog j) (by positivity)))
          (Real.exp_pos _).le
      _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h₂ (by positivity : 0 ≤ 2*A)
  have hsum : (∑ j ∈ Z.image level, r^j) ≤ (1-r)⁻¹ := by
    have h := summable_geometric_of_lt_one hr₀.le hr₁
    simpa only [tsum_geometric_of_lt_one hr₀.le hr₁] using
      (h.sum_le_tsum (Z.image level) (fun k _ => pow_nonneg hr₀.le k))
  rw [← Finset.sum_fiberwise_of_maps_to (g:=level) (t:=Z.image level)
    (fun z hz => Finset.mem_image_of_mem _ hz)]
  apply (Finset.sum_le_sum fun j _ => hs j).trans
  rw [← Finset.mul_sum]
  calc
    _ ≤ (2*A*(L+2))*(3*T) := mul_le_mul_of_nonneg_left (hsum.trans hratio) (by positivity)
    _ = _ := by dsimp [L]; ring

end GoldbachDensity

namespace GoldbachDensity

open Complex Real Finset

/-- Uniform Mellin-residue bound over an arbitrary finite set of the true
zeros of one primitive character. Each zero has its analytic multiplicity. -/
theorem primitive_gamma_zero_sum_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (hGRH : ∀ s : ℂ, 0 < s.re → s.re < 1 →
      χ.LFunction s = 0 → s.re=1/2) {z : ℂ} (hz : 0 < z.re) (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1 ∧ χ.LFunction ρ = 0) :
    let T := ‖z‖/z.re
    ‖∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℂ) * (Complex.Gamma ρ * z^(-ρ))‖ ≤
      (6*(10/Real.log (23/22))*Real.sqrt (2*Real.pi)) *
        (‖z‖^(-(1/2):ℝ)*T) * (Real.log ((q:ℝ)*(2+T))+2) := by
  let T := ‖z‖/z.re
  let A := 10/Real.log (23/22)
  let W := fun ρ => (analyticOrderNatAt χ.LFunction ρ : ℝ)
  have hq : 1 ≤ (q:ℝ) := by exact_mod_cast q.pos_of_neZero
  have hT : 1 ≤ T := (one_le_div hz).2 (Complex.re_le_norm z)
  have hA : 0 ≤ A := by dsimp [A]; positivity [Real.log_pos (by norm_num : (1:ℝ)<23/22)]
  have hc := damped_window_count (Z:=Z) (w:=W) hq hT hA (fun _ _ => Nat.cast_nonneg _)
    (fun t S hS => GoldbachDensityProgression.primitive_character_window_count χ hprim t S hGRH
      (fun ρ hρ => ⟨(hZ ρ (hS ρ hρ).1).1,(hZ ρ (hS ρ hρ).1).2.1,
        (hZ ρ (hS ρ hρ).1).2.2,(hS ρ hρ).2⟩))
  have hscale : z.re/‖z‖ = T⁻¹ := by simp [T]
  let B := Real.sqrt (2*Real.pi)*‖z‖^(-(1/2):ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (ρ : ℂ) (hρ : ρ ∈ Z) :
      ‖(analyticOrderNatAt χ.LFunction ρ : ℂ) * (Complex.Gamma ρ * z^(-ρ))‖ ≤
        B*(W ρ*Real.exp (-|ρ.im|/T)) := by
    have hp := gamma_half_mellin_decay (hGRH ρ (hZ ρ hρ).1 (hZ ρ hρ).2.1 (hZ ρ hρ).2.2) hz
    rw [hscale,show -T⁻¹*|ρ.im| = -|ρ.im|/T by ring] at hp
    rw [norm_mul,Complex.norm_natCast]
    simpa only [B,W,mul_left_comm,mul_assoc] using
      mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (α:=ℝ) (analyticOrderNatAt χ.LFunction ρ))
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum hb).trans
  rw [← Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left hc hB).trans_eq
  dsimp only [B,A,T]
  ring

end GoldbachDensity

namespace GoldbachDensityCircle

open MeasureTheory Set AddCircle Filter
open scoped Topology

private instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

/-- Reduced rational centers in the standard period, including 0/1. -/
def majorArcIndices (Q : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 Q) ×ˢ (Finset.range Q)).filter (fun i => i.2 < i.1 ∧ i.2.Coprime i.1)

theorem mem_majorArcIndices {Q : ℕ} {i : ℕ × ℕ} :
    i ∈ majorArcIndices Q ↔ 0 < i.1 ∧ i.1 ≤ Q ∧ i.2 < i.1 ∧ i.2.Coprime i.1 := by
  simp only [majorArcIndices,Finset.mem_filter,Finset.mem_product,Finset.mem_Icc,Finset.mem_range]
  omega

noncomputable def arcCenter (i : ℕ × ℕ) : ℝ := (i.2:ℝ)/i.1
noncomputable def arcWidth (X P : ℝ) (q : ℕ) := P/((q:ℝ)*X)

/-- For disjoint arcs, even intervals crossing the endpoint of a period
cannot both contain a lift of the same circle point. -/
theorem unique_arc_of_equal_lifts {Q : ℕ} {X P : ℝ} (hX : 0<X) (hP : 0 ≤ P)
    (hsmall : 2*P*Q < X) {i j : ℕ × ℕ} (hi : i ∈ majorArcIndices Q) (hj : j ∈ majorArcIndices Q)
    {s t : ℝ} (hs : |s| ≤ arcWidth X P i.1) (ht : |t| ≤ arcWidth X P j.1)
    (he : ((s+arcCenter i : ℝ) : AddCircle (1:ℝ)) = ((t+arcCenter j : ℝ) : AddCircle (1:ℝ))) :
    i = j := by
  rcases i with ⟨q,a⟩
  rcases j with ⟨r,b⟩
  obtain ⟨hq,hQ,ha,hqa⟩ := mem_majorArcIndices.mp hi
  obtain ⟨hr,hR,hb,hrb⟩ := mem_majorArcIndices.mp hj
  dsimp only at hq hQ ha hqa hr hR hb hrb
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  have hr' : 0 < (r:ℝ) := by exact_mod_cast hr
  let u := (a:ℝ)/q
  let v := (b:ℝ)/r
  change ((s+u:ℝ):AddCircle (1:ℝ)) = ((t+v:ℝ):AddCircle (1:ℝ)) at he
  obtain ⟨k,hk⟩ : ∃ k : ℤ, k • (1:ℝ) = (s+u) - (t+v) := by
    rw [← AddCircle.coe_eq_zero_iff,AddCircle.coe_sub,he,sub_self]
  rw [zsmul_eq_mul,mul_one] at hk
  let D : ℤ := a*r - b*q - k*q*r
  have hD : (D:ℝ) = (t-s)*q*r := by
    have heq : (u-v-(k:ℝ))=(t-s) := by linarith
    rw [← heq]
    dsimp [D,u,v]
    push_cast
    field_simp
  have hd : |t-s| ≤ P/((r:ℝ)*X) + P/((q:ℝ)*X) :=
    (abs_sub_le _ _ _ |>.trans_eq (by simp : _ + |(0:ℝ)-s| = _)).trans (add_le_add ht hs)
  have hDsm : |(D:ℝ)| < 1 := by
    rw [hD, abs_mul,abs_mul,abs_of_pos hq',abs_of_pos hr']
    calc
      _ ≤ (P/((r:ℝ)*X)+P/((q:ℝ)*X))*q*r :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd hq'.le) hr'.le
      _ = (P*q+P*r)/X := by field_simp
      _ < 1 := (div_lt_one hX).2 (by
        have hqQ : (q:ℝ) ≤ Q := by exact_mod_cast hQ
        have hrQ : (r:ℝ) ≤ Q := by exact_mod_cast hR
        nlinarith [mul_le_mul_of_nonneg_left hqQ hP,mul_le_mul_of_nonneg_left hrQ hP])
  have hiD : |D| < (1:ℤ) := by exact_mod_cast hDsm
  have hD0 : D=0 := by rw [abs_lt] at hiD; omega
  rw [hD0,Int.cast_zero] at hD
  have hs' : t=s := by
    have hm := (mul_eq_zero.mp hD.symm).resolve_right hr'.ne'
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hq'.ne')
  have hu : 0≤u ∧ u<1 := ⟨by dsimp [u]; positivity,(div_lt_one hq').2 (by exact_mod_cast ha)⟩
  have hv : 0≤v ∧ v<1 := ⟨by dsimp [v]; positivity,(div_lt_one hr').2 (by exact_mod_cast hb)⟩
  have hk0 : k=0 := by
    have hm : (-1:ℝ)<k := by linarith
    have hp : (k:ℝ)<1 := by linarith
    have hm' : (-1:ℤ)<k := by exact_mod_cast hm
    have hp' : k<(1:ℤ) := by exact_mod_cast hp
    omega
  rw [hk0, Int.cast_zero] at hk
  have huv : (a:ℝ)/q=(b:ℝ)/r := (show u=v by linarith)
  have hrat : (a:ℚ)/q=(b:ℚ)/r := by
    apply Rat.cast_injective (α:=ℝ)
    simpa only [Rat.cast_div,Rat.cast_natCast] using huv
  obtain ⟨h₁,h₂⟩ := Rat.div_int_inj (a:=(a:ℤ)) (b:=(q:ℤ)) (c:=(b:ℤ)) (d:=(r:ℤ))
    (by exact_mod_cast hq) (by exact_mod_cast hr) (by simpa using hqa) (by simpa using hrb)
    (by simpa using hrat)
  exact Prod.ext (by exact_mod_cast h₂) (by exact_mod_cast h₁)

noncomputable def arcCoordinate (i : ℕ × ℕ) (x : AddCircle (1:ℝ)) : ℝ :=
  (AddCircle.equivIoc 1 (-1/2) (x - (arcCenter i : AddCircle (1:ℝ))) : ℝ)

theorem lift_arcCoordinate (i : ℕ × ℕ) (x : AddCircle (1:ℝ)) :
    ((arcCoordinate i x + arcCenter i : ℝ) : AddCircle (1:ℝ)) = x := by
  rw [AddCircle.coe_add]
  simp [arcCoordinate]

noncomputable def arcTerm (X P : ℝ) (W : ℕ → ℝ → ℂ) (i : ℕ × ℕ) (x : AddCircle (1:ℝ)) : ℂ :=
  if |arcCoordinate i x| ≤ arcWidth X P i.1 then W i.1 (arcCoordinate i x) else 0

noncomputable def arcModel (X P : ℝ) (Q : ℕ) (W : ℕ → ℝ → ℂ) (x : AddCircle (1:ℝ)) :=
  ∑ i ∈ majorArcIndices Q, arcTerm X P W i x

theorem arcModel_square (X P : ℝ) (Q : ℕ) (W : ℕ → ℝ → ℂ) (hX : 0<X) (hP : 0 ≤ P)
    (hsmall : 2*P*Q<X) (x : AddCircle (1:ℝ)) :
    arcModel X P Q W x ^ 2 = ∑ i ∈ majorArcIndices Q, (arcTerm X P W i x)^2 := by
  unfold arcModel
  rw [pow_two,Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mul_sum,Finset.sum_eq_single i _ (by simp [hi]),pow_two]
  intro j hj hne
  by_cases h : |arcCoordinate i x| ≤ arcWidth X P i.1
  · have h' : ¬ |arcCoordinate j x| ≤ arcWidth X P j.1 := by
      intro hs
      exact hne (unique_arc_of_equal_lifts hX hP hsmall hj hi hs h
        ((lift_arcCoordinate j x).trans (lift_arcCoordinate i x).symm))
    simp [arcTerm,h']
  · simp [arcTerm,h]

theorem measurable_arcCoordinate (i : ℕ × ℕ) : Measurable (arcCoordinate i) :=
  (measurable_subtype_coe.comp (AddCircle.measurableEquivIoc 1 (-1/2)).measurable).comp
    (measurable_id.sub_const _)

theorem arcTerm_memLp (X P : ℝ) (W : ℕ → ℝ → ℂ) (i : ℕ × ℕ) (hW : Continuous (W i.1))
    (p : ENNReal) : MemLp (arcTerm X P W i) p haarAddCircle := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-(arcWidth X P i.1)) (arcWidth X P i.1)) hW.continuousOn
  have hc := measurable_arcCoordinate i
  apply MemLp.of_bound (C := max C 0)
  · exact (Measurable.ite (measurableSet_le hc.abs measurable_const)
      (hW.measurable.comp hc) measurable_const).aestronglyMeasurable
  · filter_upwards with x
    by_cases h : |arcCoordinate i x| ≤ arcWidth X P i.1
    · simpa [arcTerm,h] using (hC _ (abs_le.mp h)).trans (le_max_left _ 0)
    · simp [arcTerm,h]

theorem arcModel_memLp (X P : ℝ) (Q : ℕ) (W : ℕ → ℝ → ℂ) (hW : ∀ q, Continuous (W q))
    (p : ENNReal) : MemLp (arcModel X P Q W) p haarAddCircle := by
  exact memLp_finsetSum (majorArcIndices Q) (f:=arcTerm X P W)
    (fun i _ => arcTerm_memLp X P W i (hW _) p)

/-- Translation by a circle point multiplies the Fourier coefficients by its character. -/
theorem fourierCoeff_translate (c : AddCircle (1:ℝ)) (g : AddCircle (1:ℝ) → ℂ) (n : ℤ) :
    fourierCoeff (fun x => g (x-c)) n = fourier (-n) c * fourierCoeff g n := by
  let f := fun x : AddCircle (1:ℝ) => fourier (-n) x * g (x-c)
  change (∫ x, f x ∂haarAddCircle) = _
  rw [← integral_add_right_eq_self (μ:=haarAddCircle) f c, fourierCoeff, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [f,add_sub_cancel_right,smul_eq_mul,fourier_apply,zsmul_add,toCircle_add,Circle.coe_mul]
  ring

private theorem arcTerm_square_coeff (X P : ℝ) (W : ℕ → ℝ → ℂ) (i : ℕ × ℕ)
    (hh : 0 ≤ arcWidth X P i.1) (hsmall : arcWidth X P i.1 < 1/2) (k : ℤ) :
    fourierCoeff (fun x => (arcTerm X P W i x)^2) k =
      fourier (-k) (arcCenter i : AddCircle (1:ℝ)) *
        ∫ t : ℝ in -(arcWidth X P i.1)..arcWidth X P i.1,
          fourier (-k) (t : AddCircle (1:ℝ)) * W i.1 t ^ 2 := by
  let w := arcWidth X P i.1
  let C := fun t : ℝ => (Icc (-w) w).indicator (fun b => W i.1 b ^ 2) t
  let g := AddCircle.liftIoc 1 (-1/2:ℝ) C
  have he : (fun x => (arcTerm X P W i x)^2) =
      fun x => g (x-(arcCenter i : AddCircle (1:ℝ))) := by
    funext x
    let t := arcCoordinate i x
    change (if |t| ≤ w then W i.1 t else 0)^2 = C t
    by_cases h : |t| ≤ w
    · simp [C,h,abs_le.mp h]
    · simp [C,h,show t ∉ Icc (-w) w from fun ht => h (abs_le.mpr ht)]
  rw [he,fourierCoeff_translate]
  congr 1
  rw [fourierCoeff_eq_intervalIntegral _ _ (-1/2:ℝ)]
  simp only [div_one,one_smul]
  let f := fun t : ℝ => fourier (-k) (t : AddCircle (1:ℝ)) * W i.1 t ^ 2
  have eqI : (∫ t : ℝ in (-1/2:ℝ)..(-1/2+1:ℝ), fourier (-k) (t : AddCircle (1:ℝ)) • g t) =
      ∫ t : ℝ in (-1/2:ℝ)..(-1/2+1:ℝ), (Icc (-w) w).indicator f t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    rw [uIoc_of_le (by norm_num)] at ht
    change _ • AddCircle.liftIoc 1 (-1/2:ℝ) C t = _
    rw [AddCircle.liftIoc_coe_apply ht,smul_eq_mul]
    by_cases h : t ∈ Icc (-w) w <;> simp [C,f,h]
  rw [eqI,intervalIntegral.integral_of_le (by norm_num),
    integral_indicator measurableSet_Icc,Measure.restrict_restrict measurableSet_Icc,
    intervalIntegral.integral_of_le (by dsimp [w] at *; linarith)]
  have hsub : Icc (-w) w ⊆ Ioc (-1/2:ℝ) (-1/2+1) :=
    fun x hx => ⟨by linarith [hx.1],by linarith [hx.2]⟩
  rw [inter_eq_left.mpr hsub]
  exact setIntegral_congr_set Ioc_ae_eq_Icc.symm

/-- Exact separated formula for the coefficients of the squared major-arc
model with arbitrary continuous profiles at the reduced rational centers. -/
theorem arcModel_square_coeff (X P : ℝ) (Q : ℕ) (W : ℕ → ℝ → ℂ) (hW : ∀ q, Continuous (W q))
    (hX : 0<X) (hP : 0≤P) (hsmall : 2*P*Q<X) (n : ℤ) :
    fourierCoeff (fun x => arcModel X P Q W x ^ 2) n =
      ∑ i ∈ majorArcIndices Q, fourier (-n) (arcCenter i : AddCircle (1:ℝ)) *
        ∫ t : ℝ in -(arcWidth X P i.1)..arcWidth X P i.1,
          fourier (-n) (t : AddCircle (1:ℝ)) * W i.1 t ^ 2 := by
  let f := fun (i : ℕ × ℕ) (x : AddCircle (1:ℝ)) => arcTerm X P W i x ^ 2
  have he : (fun x => arcModel X P Q W x ^ 2) = ∑ i ∈ majorArcIndices Q, f i := by
    funext x
    simpa only [f,Finset.sum_apply] using arcModel_square X P Q W hX hP hsmall x
  have hint (i : ℕ × ℕ) : Integrable (f i) haarAddCircle := by
    let F := arcTerm X P W i
    have hF : MemLp F 2 haarAddCircle := arcTerm_memLp X P W i (hW _) _
    simpa only [f,F,pow_two] using
      (memLp_one_iff_integrable.mp (hF.fun_mul hF : MemLp (fun t => F t * F t) 1 haarAddCircle))
  rw [he,fourierCoeff.sum _ _ (fun i _ => hint i),Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  obtain ⟨hq,hQ,_,_⟩ := mem_majorArcIndices.mp hi
  have hq' : 1 ≤ (i.1:ℝ) := by exact_mod_cast hq
  have hQ' : 1 ≤ (Q:ℝ) := by exact_mod_cast hq.trans_le hQ
  apply arcTerm_square_coeff X P W i (div_nonneg hP (by positivity))
  apply (div_lt_iff₀ (mul_pos (by linarith) hX)).2
  nlinarith [mul_le_mul_of_nonneg_left hQ' hP,mul_le_mul_of_nonneg_right hq' hX.le]

theorem arcModel_eq_of_mem {X P : ℝ} {Q : ℕ} (W : ℕ → ℝ → ℂ) (hX : 0<X) (hP : 0≤P)
    (hsmall : 2*P*Q<X) (x : AddCircle (1:ℝ)) {i : ℕ × ℕ} (hi : i ∈ majorArcIndices Q)
    (h : |arcCoordinate i x| ≤ arcWidth X P i.1) :
    arcModel X P Q W x = W i.1 (arcCoordinate i x) := by
  unfold arcModel
  rw [Finset.sum_eq_single_of_mem i hi]
  · simp [arcTerm,h]
  · intro j hj hne
    have hnot : ¬ |arcCoordinate j x| ≤ arcWidth X P j.1 := by
      intro h'
      exact hne (unique_arc_of_equal_lifts hX hP hsmall hj hi h' h
        ((lift_arcCoordinate j x).trans (lift_arcCoordinate i x).symm))
    simp [arcTerm,hnot]

theorem arcModel_eq_zero_of_not_mem {X P : ℝ} {Q : ℕ} (W : ℕ → ℝ → ℂ)
    (x : AddCircle (1:ℝ)) (h : ∀ i ∈ majorArcIndices Q, arcWidth X P i.1 < |arcCoordinate i x|) :
    arcModel X P Q W x = 0 :=
  Finset.sum_eq_zero fun i hi => ite_eq_right (not_le.mpr (h i hi))

theorem sum_arcIndices {M : Type*} [AddCommMonoid M] (Q : ℕ) (f : ℕ × ℕ → M) :
    ∑ i ∈ majorArcIndices Q, f i =
      ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q), f (q,a) := by
  classical
  rw [majorArcIndices,Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  have hsub := (Finset.mem_Icc.mp hq).2
  rw [← Finset.sum_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter,Finset.mem_range]
  omega

/-- The energy of the major-arc model is the sum of profile energies over
disjoint real intervals; the translation of an arc does not change its mass. -/
theorem arcModel_energy (X P : ℝ) (Q : ℕ) (W : ℕ → ℝ → ℂ) (hW : ∀ q, Continuous (W q))
    (hX : 0<X) (hP : 0≤P) (hsmall : 2*P*Q<X) :
    (∫ x, ‖arcModel X P Q W x‖^2 ∂haarAddCircle) =
      ∑ i ∈ majorArcIndices Q, ∫ t : ℝ in -(arcWidth X P i.1)..arcWidth X P i.1, ‖W i.1 t‖^2 := by
  let U (q : ℕ) (t : ℝ) : ℂ := ‖W q t‖
  have he (x : AddCircle (1:ℝ)) : arcModel X P Q U x = (‖arcModel X P Q W x‖ : ℂ) := by
    by_cases h : ∃ i ∈ majorArcIndices Q, |arcCoordinate i x| ≤ arcWidth X P i.1
    · obtain ⟨i,hi,hw⟩ := h
      rw [arcModel_eq_of_mem W hX hP hsmall x hi hw,arcModel_eq_of_mem U hX hP hsmall x hi hw]
    · push Not at h
      rw [arcModel_eq_zero_of_not_mem W x h,arcModel_eq_zero_of_not_mem U x h]
      simp
  have H := arcModel_square_coeff X P Q U (fun q => Complex.continuous_ofReal.comp (hW q).norm)
    hX hP hsmall 0
  simp only [fourierCoeff,neg_zero,fourier_zero,one_smul,one_mul,he,U,← Complex.ofReal_pow,
    integral_complex_ofReal,intervalIntegral.integral_ofReal,← Complex.ofReal_sum] at H
  exact Complex.ofReal_injective H

end GoldbachDensityCircle

namespace GoldbachDensityCircle

open AddCircle Set

/-- A point of the unit circle has a reduced nearby rational with canonical
numerator; the only discrepancy in passing from a real approximation to
the canonical center is an integral period. -/
theorem exists_rational_arc_approximation (x : AddCircle (1:ℝ)) (M : ℕ) (hM : 0<M) :
    ∃ i ∈ majorArcIndices M, ∃ β : ℝ,
      x = ((β + arcCenter i : ℝ) : AddCircle (1:ℝ)) ∧ |β| ≤ 1 / (((M:ℝ)+1)*i.1) := by
  let t : ℝ := AddCircle.equivIco 1 0 x
  obtain ⟨r,hr,hrM⟩ := Real.exists_rat_abs_sub_le_and_den_le t hM
  let f : ℚ := Int.fract r
  have hf₀ : 0≤f := Int.fract_nonneg r
  have hf₁ : f<1 := Int.fract_lt_one _
  have fd : f.den = r.den := Rat.den_intFract _
  have hn : 0 ≤ f.num := Rat.num_nonneg.mpr hf₀
  have hden : 0 < (f.den:ℚ) := by exact_mod_cast f.pos
  have he' : (f.num:ℚ)/f.den=f := Rat.num_div_den f
  have hcast : (f.num.natAbs : ℤ)=f.num := Int.natAbs_of_nonneg hn
  have he : (f.num.natAbs:ℚ)/f.den=f := by
    have hc : (f.num.natAbs : ℚ) = f.num := by
      simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ℚ)) hcast
    rw [hc,he']
  have hnumlt : f.num.natAbs < f.den := by
    have hh : (f.num.natAbs : ℚ) < f.den := (div_lt_one hden).1 (he.trans_lt hf₁)
    exact_mod_cast hh
  let i : ℕ × ℕ := (f.den, f.num.natAbs)
  have hi : i ∈ majorArcIndices M := mem_majorArcIndices.mpr
    ⟨f.pos,fd.le.trans hrM,hnumlt,f.reduced⟩
  refine ⟨i,hi,t-(r:ℝ),?_,?_⟩
  · have ht : (t : AddCircle (1:ℝ))=x := AddCircle.coe_equivIco
    have hcenter : arcCenter i = (f:ℝ) := by
      have hh := congrArg (fun z : ℚ => (z:ℝ)) he
      simpa [i,arcCenter] using hh
    have hf : (f:ℝ) = (r:ℝ) - (⌊r⌋ : ℤ) := by
      change (((r - ⌊r⌋ : ℚ) : ℝ)) = _
      rw [Rat.cast_sub,Rat.cast_intCast]
    rw [hcenter,hf,show t-(r:ℝ)+((r:ℝ)-(⌊r⌋:ℤ))=t-(⌊r⌋:ℤ) by ring,AddCircle.coe_sub,ht]
    have hz : (((⌊r⌋ : ℤ) : ℝ) : AddCircle (1:ℝ)) = 0 :=
      (AddCircle.coe_eq_zero_iff (1:ℝ)).mpr ⟨⌊r⌋, by simp⟩
    rw [hz,sub_zero]
  · simpa only [i,fd] using hr

theorem arcWidth_lt_half {X P : ℝ} {Q q : ℕ} (hX : 0<X) (hP : 0≤P)
    (hsmall : 2*P*Q<X) (hq : 0<q) (hQ : q≤Q) : arcWidth X P q < 1/2 := by
  have hq' : 1 ≤ (q:ℝ) := by exact_mod_cast hq
  have hQ' : 1 ≤ (Q:ℝ) := by exact_mod_cast hq.trans_le hQ
  apply (div_lt_iff₀ (mul_pos (by linarith) hX)).2
  nlinarith [mul_le_mul_of_nonneg_left hQ' hP,mul_le_mul_of_nonneg_right hq' hX.le]

theorem arcCoordinate_of_lift {i : ℕ × ℕ} {x : AddCircle (1:ℝ)} {β : ℝ}
    (hβ : |β|<1/2) (h : x = ((β+arcCenter i : ℝ):AddCircle (1:ℝ))) :
    arcCoordinate i x = β := by
  rw [h,arcCoordinate,AddCircle.coe_add,add_sub_cancel_right]
  apply AddCircle.equivIoc_coe_of_mem
  have hh := abs_lt.mp hβ
  exact ⟨by linarith [hh.1],by linarith [hh.2]⟩

/-- Near rationals the assumed local formula determines the major-arc model.
Away from the major arcs, it suffices to bound a single rational main term
whose denominator or whose offset exceeds the major-arc cutoff. -/
theorem global_error_of_rational_approximations {X P R A B : ℝ} {M Q : ℕ}
    (F : AddCircle (1:ℝ) → ℂ) (W : ℕ → ℝ → ℂ)
    (hX : 0<X) (hP : 0≤P) (hsmall : 2*P*Q<X) (hM : 0<M) (hQM : Q≤M)
    (hdir : 1/((M:ℝ)+1) ≤ R) (hwidth : P/X ≤ R) (hB : 0≤B)
    (hloc : ∀ i ∈ majorArcIndices M, ∀ β : ℝ, |β| ≤ R/i.1 →
      ‖F ((β+arcCenter i : ℝ):AddCircle (1:ℝ))-W i.1 β‖ ≤ A)
    (hminor : ∀ i ∈ majorArcIndices M, ∀ β : ℝ, |β| ≤ R/i.1 →
      (Q < i.1 ∨ P<(i.1:ℝ)*X*|β|) → ‖W i.1 β‖ ≤ B) :
    ∀ x, ‖F x-arcModel X P Q W x‖ ≤ A+B := by
  intro x
  by_cases h : ∃ i ∈ majorArcIndices Q, |arcCoordinate i x| ≤ arcWidth X P i.1
  · obtain ⟨i,hi,hh⟩ := h
    obtain ⟨hq,hqQ,ha,hcop⟩ := mem_majorArcIndices.mp hi
    have hi' := mem_majorArcIndices.mpr ⟨hq,hqQ.trans hQM,ha,hcop⟩
    have hw : arcWidth X P i.1 ≤ R/i.1 := by
      unfold arcWidth
      rw [mul_comm,← div_div]
      exact div_le_div_of_nonneg_right hwidth (by positivity)
    have hloc' := hloc i hi' (arcCoordinate i x) (hh.trans hw)
    rw [lift_arcCoordinate] at hloc'
    rw [arcModel_eq_of_mem W hX hP hsmall x hi hh]
    linarith
  · push Not at h
    rw [arcModel_eq_zero_of_not_mem W x h,sub_zero]
    obtain ⟨i,hi,β,hx,hβ⟩ := exists_rational_arc_approximation x M hM
    obtain ⟨hq,_,ha,hcop⟩ := mem_majorArcIndices.mp hi
    have hq' : 0<(i.1:ℝ) := by exact_mod_cast hq
    have hh : |β| ≤ R/i.1 := hβ.trans (by rw [← div_div]; exact div_le_div_of_nonneg_right hdir hq'.le)
    have hs : Q < i.1 ∨ P<(i.1:ℝ)*X*|β| := by
      by_cases hden : Q < i.1
      · exact Or.inl hden
      right
      by_contra! hd
      have hden' : i.1≤Q := le_of_not_gt hden
      have hbound : |β|≤arcWidth X P i.1 := (le_div_iff₀ (mul_pos hq' hX)).2 (by linarith only [hd, mul_comm ((i.1:ℝ)*X) |β|])
      have he := arcCoordinate_of_lift (hbound.trans_lt (arcWidth_lt_half hX hP hsmall hq hden')) hx
      have hiQ : i ∈ majorArcIndices Q := mem_majorArcIndices.mpr ⟨hq,hden',ha,hcop⟩
      exact (not_le.mpr (h i hiQ)) (he ▸ hbound)
    have hloc' := hloc i hi β hh
    rw [← hx] at hloc'
    calc
      _ ≤ ‖F x-W i.1 β‖ + ‖W i.1 β‖ := norm_le_norm_sub_add _ _
      _ ≤ _ := add_le_add hloc' (hminor i hi β hh hs)

end GoldbachDensityCircle

namespace GoldbachDensity

open Complex Finset

/-- Fourier phase at a rational point of the unit circle. -/
noncomputable def rationalPhase (n q a : ℕ) : ℂ :=
  Complex.exp (-2*Real.pi*I*n*(a:ℂ)/q)

theorem complete_rational_sum {q : ℕ} (hq : 0 < q) (n : ℕ) :
    (∑ a ∈ range q, rationalPhase n q a) = if q ∣ n then (q:ℂ) else 0 := by
  let z := Complex.exp (2*Real.pi*I*(((-1:ℤ):ℂ)/q))
  have hz : IsPrimitiveRoot z q := by
    simpa [z,mul_div_assoc] using Complex.isPrimitiveRoot_exp_of_isCoprime (-1) q hq.ne'
      (show IsCoprime (-1:ℤ) ↑q from ⟨-1,0,by ring⟩)
  have hp (a : ℕ) : rationalPhase n q a = (z^n)^a := by
    dsimp only [rationalPhase,z]
    rw [← exp_nat_mul,← exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [hp]
  split_ifs with h
  · simp [(hz.pow_eq_one_iff_dvd n).mpr h]
  · have h₁ : z^n ≠ 1 := mt (hz.pow_eq_one_iff_dvd n).mp h
    have hq' : (z^n)^q = 1 := by rw [← pow_mul,mul_comm,pow_mul,hz.pow_eq_one,one_pow]
    have hh := geom_sum_mul (z^n) q
    rw [hq',sub_self,mul_eq_zero] at hh
    exact hh.resolve_right (sub_ne_zero.mpr h₁)

private theorem phase_multiples {d k : ℕ} (hd : 0<d) (hk : 0<k) (n : ℕ) :
    (∑ a ∈ (range (d*k)).filter (fun a => d ∣ a), rationalPhase n (d*k) a) =
      if k∣n then (k:ℂ) else 0 := by
  have he : (range (d*k)).filter (fun a => d∣a) = (range k).image (fun j => d*j) := by
    ext a
    simp only [mem_filter,mem_range,mem_image]
    constructor
    · rintro ⟨hlt,j,rfl⟩
      exact ⟨j,(Nat.mul_lt_mul_left hd).mp hlt,rfl⟩
    · rintro ⟨j,hj,rfl⟩
      exact ⟨Nat.mul_lt_mul_of_pos_left hj hd,dvd_mul_right ..⟩
  rw [he,Finset.sum_image (fun i _ j _ h => Nat.eq_of_mul_eq_mul_left hd h)]
  apply Eq.trans _ (complete_rational_sum hk n)
  apply sum_congr rfl
  intro j _
  unfold rationalPhase
  congr 1
  push_cast
  have hh : (d:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

private theorem support_prod_dvd {s : Finset ℕ} (h : ∀ p∈s, Nat.Prime p) (a : ℕ) :
    (∏ p ∈ s, p) ∣ a ↔ ∀ p∈s, p ∣ a := by
  constructor
  · intro hdiv p hp
    exact (dvd_prod_of_mem id hp).trans hdiv
  · classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert p S hp ih =>
      intro hall
      rw [prod_insert hp]
      have hP := h p (mem_insert_self ..)
      have hs q hq := h q (mem_insert_of_mem hq)
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · apply Nat.coprime_prod_right_iff.mpr
        intro q hq
        exact (Nat.coprime_primes hP (hs q hq)).mpr (fun e => hp (e ▸ hq))
      · exact hall p (mem_insert_self ..)
      · exact ih hs (fun q hq => hall q (mem_insert_of_mem hq))

private theorem primitive_ind {S : Finset ℕ} (h : ∀ p∈S, Nat.Prime p) (a : ℕ) :
    (if a.Coprime (∏ p ∈ S,p) then (1:ℂ) else 0) =
      ∑ s ∈ S.powerset, if (∏ p∈s,p) ∣ a then (-1:ℂ)^s.card else 0 := by
  let f := fun p : ℕ => if p∣a then (-1:ℂ) else 0
  have he : (if a.Coprime (∏ p∈S,p) then (1:ℂ) else 0) = ∏ p∈S, (1+f p) := by
    by_cases hc : a.Coprime (∏ p∈S,p)
    · rw [ite_eq_left hc]
      symm
      apply prod_eq_one
      intro p hp
      have hd := (h p hp).coprime_iff_not_dvd.mp ((Nat.coprime_prod_right_iff.mp hc p hp).symm)
      simp [f,hd]
    · rw [ite_eq_right hc]
      rw [Nat.coprime_prod_right_iff] at hc
      push Not at hc
      obtain ⟨p,hp,hh⟩ := hc
      have hd : p ∣ a := by
        by_contra hd
        exact hh (((h p hp).coprime_iff_not_dvd.mpr hd).symm)
      symm
      exact prod_eq_zero hp (by simp [f,hd])
  rw [he,Finset.prod_one_add]
  apply sum_congr rfl
  intro s hs
  have hs' := mem_powerset.mp hs
  simp only [f,Finset.prod_ite_zero,prod_const]
  simp only [support_prod_dvd (fun p hp => h p (hs' hp)) a]

/-- The Ramanujan sum at a squarefree denominator, including the denominator
one. The proof expands the coprimality condition over prime divisors and
sums complete geometric progressions. -/
theorem squarefree_ramanujan_sum (S : Finset ℕ) (hS : ∀ p∈S, Nat.Prime p) (n : ℕ) :
    (∑ a ∈ (range (∏ p∈S,p)).filter (fun a => a.Coprime (∏ p∈S,p)),
      rationalPhase n (∏ p∈S,p) a) =
      ∏ p∈S, ((if p∣n then (p:ℂ) else 0) - 1) := by
  classical
  let Q := fun s : Finset ℕ => ∏ p∈s,p
  let g := fun p : ℕ => if p∣n then (p:ℂ) else 0
  have hsplit : (∏ p∈S, (g p-1)) = ∑ s ∈ S.powerset, (-1:ℂ)^s.card * ∏ p∈S\s,g p := by
    simpa only [sub_eq_add_neg,add_comm _ (-1:ℂ),prod_const] using
      (Finset.prod_add (fun _ : ℕ => (-1:ℂ)) g S)
  rw [show (∏ p∈S, ((if p∣n then (p:ℂ) else 0)-1)) = (∏ p∈S,(g p-1)) from rfl,hsplit,sum_filter]
  have hterm (a : ℕ) : (if a.Coprime (Q S) then rationalPhase n (Q S) a else 0) =
      ∑ s ∈ S.powerset, (-1:ℂ)^s.card * (if Q s∣a then rationalPhase n (Q S) a else 0) := by
    have h := congrArg (fun z : ℂ => z * rationalPhase n (Q S) a) (primitive_ind hS a)
    change (if a.Coprime (Q S) then (1:ℂ) else 0)*_ = _ at h
    rw [sum_mul] at h
    calc
      _ = (if a.Coprime (Q S) then (1:ℂ) else 0)*rationalPhase n (Q S) a := by split_ifs <;> simp
      _ = _ := h
      _ = _ := by
        apply sum_congr rfl
        intro s _
        change (if Q s ∣ a then _ else _) * _ = _
        by_cases hd : Q s∣a <;> simp [hd]
  change (∑ a ∈ range (Q S), (if a.Coprime (Q S) then rationalPhase n (Q S) a else 0)) = _
  simp_rw [hterm]
  rw [sum_comm]
  apply sum_congr rfl
  intro s hs
  rw [← mul_sum,← sum_filter]
  apply congrArg ((-1:ℂ)^s.card * ·)
  have hs' := mem_powerset.mp hs
  let t := S\s
  have ht : t ⊆ S := sdiff_subset
  have hfactor : Q S = Q s*Q t := (Finset.prod_sdiff hs' : Q t*Q s = Q S).symm.trans (mul_comm ..)
  have hq {s : Finset ℕ} (hs : s ⊆ S) : 0 < Q s :=
    prod_pos (fun p hp => (hS p (hs hp)).pos)
  rw [hfactor,phase_multiples (hq hs') (hq ht)]
  simp only [g,Finset.prod_ite_zero]
  simp only [show Q t ∣ n ↔ ∀ p∈t,p∣n from support_prod_dvd (fun p hp => hS p (ht hp)) n]
  split_ifs
  · dsimp [Q,t]; push_cast; rfl
  · rfl

/-- At coprime frequency the sum over reduced residues is the Möbius
function, including the vanishing case at nonsquarefree moduli. -/
theorem coprime_ramanujan_eq_moebius {q n : ℕ} (hq : 0 < q) (hn : n.Coprime q) :
    (∑ j ∈ (range q).filter (fun j => j.Coprime q), rationalPhase n q j) =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  classical
  let S := q.primeFactors
  let Q := fun s : Finset ℕ => ∏ p∈s,p
  have hprime {p} (hp : p ∈ S) : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
  have hsub {s : Finset ℕ} (hs : s ⊆ S) : Q s ∣ q :=
    (prod_dvd_prod_of_subset s S id hs).trans (Nat.prod_primeFactors_dvd q)
  by_cases hsq : Squarefree q
  · have heq : Q S = q := Nat.prod_primeFactors_of_squarefree hsq
    have hsum := squarefree_ramanujan_sum S (fun _ => hprime) n
    change (∑ j ∈ (range (Q S)).filter (fun j => j.Coprime (Q S)), rationalPhase n (Q S) j) = _ at hsum
    rw [heq] at hsum
    rw [hsum,ArithmeticFunction.moebius_apply_of_squarefree hsq]
    have hcard : S.card = ArithmeticFunction.cardFactors q :=
      (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hq.ne').mpr hsq
    push_cast
    rw [← hcard,← Finset.prod_const]
    apply prod_congr rfl
    intro p hp
    have hnd : ¬p∣n := fun h => (hprime hp).ne_one
      (Nat.eq_one_of_dvd_coprimes hn h (Nat.mem_primeFactors.mp hp).2.1)
    simp [hnd]
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq,Int.cast_zero,sum_filter]
    have hcop (j : ℕ) : j.Coprime q ↔ j.Coprime (Q S) := by
      constructor
      · intro hc
        exact hc.coprime_dvd_right (hsub (Subset.rfl))
      · intro hc
        apply Nat.coprime_of_dvd
        intro p hp hpj hpq
        have hmem : p∈S := Nat.mem_primeFactors.mpr ⟨hp,hpq,hq.ne'⟩
        exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hc hpj (dvd_prod_of_mem id hmem))
    have hterm (j : ℕ) : (if j.Coprime q then rationalPhase n q j else 0) =
        ∑ s ∈ S.powerset, (-1:ℂ)^s.card * (if Q s∣j then rationalPhase n q j else 0) := by
      rw [if_congr (hcop j) rfl rfl]
      have h := congrArg (fun z : ℂ => z * rationalPhase n q j) (primitive_ind (fun _ => hprime) j)
      change (if j.Coprime (Q S) then (1:ℂ) else 0)*_ = _ at h
      rw [sum_mul] at h
      calc
        _ = (if j.Coprime (Q S) then (1:ℂ) else 0)*rationalPhase n q j := by split_ifs <;> simp
        _ = _ := h
        _ = _ := by
          apply sum_congr rfl
          intro s _
          change (if Q s∣j then _ else _) * _ = _
          by_cases hd : Q s∣j <;> simp [hd]
    simp_rw [hterm]
    rw [sum_comm]
    apply sum_eq_zero
    intro s hs
    rw [← mul_sum,← sum_filter]
    have hss := mem_powerset.mp hs
    obtain ⟨k,hk⟩ := hsub hss
    have hd : 0<Q s := prod_pos (fun p hp => (hprime (hss hp)).pos)
    have hkpos : 0<k := by by_contra! hh; simp [Nat.eq_zero_of_le_zero hh] at hk; omega
    have hkn : ¬k∣n := by
      intro hkdiv
      have hkone := Nat.eq_one_of_dvd_coprimes hn hkdiv (hk ▸ dvd_mul_left k (Q s))
      have hqeq : q=Q s := by simpa [hkone] using hk
      have hsqp := binaryShift_squarefree_prod_primeFactors (Q s)
      have hf : (Q s).primeFactors = s := Nat.primeFactors_prod (fun p hp => hprime (hss hp))
      rw [hf] at hsqp
      exact hsq (hqeq ▸ hsqp)
    rw [hk,phase_multiples hd hkpos,ite_eq_right hkn,mul_zero]

end GoldbachDensity

namespace GoldbachDensity

open Complex Finset MeasureTheory Set Filter
open scoped Topology Interval

/-- Archimedean coefficient on an interval of half-width P/(q X). -/
noncomputable def dampedArcIntegral (X : ℝ) (P q n : ℕ) : ℂ :=
  let h := (P:ℝ)/(q*X)
  ∫ b : ℝ in -h..h, Complex.exp ((↑(-2*Real.pi*b*n):ℂ)*I) / ((X⁻¹:ℝ)-2*(Real.pi:ℂ)*b*I)^2

/-- The rational components of the squared major-arc model after summing
over primitive numerators, indexed here by the prime support of each
squarefree denominator. -/
noncomputable def majorArcCoefficient (X : ℝ) (P n : ℕ) : ℂ :=
  ∑ s ∈ (primesThrough P).powerset, if modulusOf s ≤ P then
    (localProduct n s : ℂ) * dampedArcIntegral X P (modulusOf s) n else 0

private theorem pos_modulus_of_mem {P : ℕ} {s : Finset ℕ} (hs : s ∈ (primesThrough P).powerset) :
    0 < modulusOf s := Finset.prod_pos fun _ hp =>
  (mem_filter.mp ((mem_powerset.mp hs) hp)).2.pos

theorem majorArcCoefficient_error {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ {X : ℝ} {P n : ℕ}, 0 < X → 0 < P → 0 < n →
    ‖majorArcCoefficient X P n -
      ((truncatedSingular n P * (n * Real.exp (-(n:ℝ)/X)) : ℝ):ℂ)‖ ≤
      2*X/Real.sqrt P * (A*(n:ℝ)^ε) := by
  obtain ⟨A,hA,hweight⟩ := weighted_euler_bound hε
  refine ⟨A,hA,?_⟩
  intro X P n hX hP hn
  have hPr : 0<(P:ℝ) := Nat.cast_pos.mpr hP
  have hPs := Real.sqrt_pos.mpr hPr
  let T := (primesThrough P).powerset
  let v : ℂ := ((n * Real.exp (-(n:ℝ)/X) : ℝ) : ℂ)
  let d (s : Finset ℕ) : ℂ := if modulusOf s ≤ P then
    (localProduct n s : ℂ)*(dampedArcIntegral X P (modulusOf s) n-v) else 0
  have heq : majorArcCoefficient X P n - ((truncatedSingular n P * (n*Real.exp (-(n:ℝ)/X)) : ℝ):ℂ)
      = ∑ s ∈ T, d s := by
    unfold majorArcCoefficient truncatedSingular
    push_cast
    rw [sum_mul,← sum_sub_distrib]
    apply sum_congr rfl
    intro s _
    by_cases h : modulusOf s ≤ P <;> simp [d,v,h,mul_sub]
  have herr (s : Finset ℕ) (hs : s ∈ T) : ‖d s‖ ≤ (2*X/Real.sqrt P) *
      (Real.sqrt (modulusOf s) * |localProduct n s|) := by
    have hq := pos_modulus_of_mem hs
    have hqr : 0 < (modulusOf s:ℝ) := Nat.cast_pos.mpr hq
    dsimp only [d]
    split_ifs with h
    · have hcut := truncated_archimedean_error (inv_pos.mpr hX) (Nat.cast_pos.mpr hn)
        (div_pos hPr (mul_pos hqr hX))
      have hv : (n:ℂ)*Complex.exp ((-(X⁻¹:ℝ):ℂ)*n) = v := by
        unfold v
        push_cast
        congr 2
        ring
      simp only [Complex.ofReal_natCast] at hcut
      rw [hv] at hcut
      have hcut' : ‖dampedArcIntegral X P (modulusOf s) n - v‖ ≤ 2*(modulusOf s:ℝ)*X/P :=
        hcut.trans_eq (by field_simp)
      have hsqr := Real.sq_sqrt hPr.le
      have hsqq := Real.sq_sqrt hqr.le
      have hsl := Real.sqrt_le_sqrt (by exact_mod_cast h : (modulusOf s:ℝ)≤P)
      have hbound : 2*(modulusOf s:ℝ)*X/P ≤ 2*X/Real.sqrt P*Real.sqrt (modulusOf s) := by
        rw [div_mul_eq_mul_div,div_le_div_iff₀ hPr hPs]
        have ht := mul_le_mul_of_nonneg_left hsl (Real.sqrt_nonneg (modulusOf s))
        calc
          _ = (2*X*Real.sqrt (P:ℝ))*(Real.sqrt (modulusOf s)*Real.sqrt (modulusOf s)) := by
            rw [← sq,hsqq]; ring
          _ ≤ (2*X*Real.sqrt (P:ℝ))*(Real.sqrt (modulusOf s)*Real.sqrt (P:ℝ)) :=
            mul_le_mul_of_nonneg_left ht (by positivity)
          _ = _ := by linear_combination (2*X*Real.sqrt (modulusOf s))*hsqr
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      apply (mul_le_mul_of_nonneg_left (hcut'.trans hbound) (abs_nonneg _)).trans_eq
      ring
    · rw [norm_zero]
      positivity
  rw [heq]
  apply (norm_sum_le ..).trans ((sum_le_sum herr).trans _)
  rw [← mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [show T = (primesThrough P).powerset from rfl, weighted_singular_sum]
  exact hweight n P hn

/-- A uniform lower bound for the actual truncated, damped model coefficient
on even indices in the upper half of the dyadic interval. -/
theorem majorArcCoefficient_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ P₀ : ℕ, ∀ (P n : ℕ) (X : ℝ), P₀ ≤ P → 0 < X →
      X/2 ≤ n → (n:ℝ) ≤ X → n ≤ P^4 → Even n → c*X ≤ ‖majorArcCoefficient X P n‖ := by
  obtain ⟨A,hA,hErr⟩ := majorArcCoefficient_error (by norm_num : 0 < (1/16:ℝ))
  obtain ⟨P₁,hPos⟩ := truncated_singular_positive
  let c := Real.exp (-1)/8
  have hc : 0 < c := by unfold c; positivity
  have ht := (tendsto_rpow_atTop (show 0<(1/4:ℝ) by norm_num)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  obtain ⟨P₂,hP₂⟩ := Filter.eventually_atTop.mp (ht.eventually_ge_atTop (2*A/c))
  refine ⟨c,hc,max 2 (max P₁ P₂),?_⟩
  intro P n X hP hX hhalf hnx hsize heven
  have hn : 0<n := by exact_mod_cast (show 0<(n:ℝ) by linarith)
  have hPr : 0<(P:ℝ) := by exact_mod_cast (by omega : 0<P)
  have hs := Real.sqrt_pos.mpr hPr
  have h₁ := hPos P (by omega) n hn hsize heven
  have h₂ := hP₂ P (by omega)
  change 2*A/c ≤ (P:ℝ)^(1/4:ℝ) at h₂
  have hsmall : (n:ℝ)^(1/16:ℝ) ≤ (P:ℝ)^(1/4:ℝ) := by
    apply (Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hsize : (n:ℝ)≤(P:ℝ)^4)
      (by norm_num : 0 ≤ (1/16:ℝ))).trans_eq
    rw [← Real.rpow_natCast (P:ℝ) 4,← Real.rpow_mul hPr.le]
    norm_num
  have hsq : (P:ℝ)^(1/4:ℝ)*(P:ℝ)^(1/4:ℝ) = Real.sqrt P := by
    rw [← Real.rpow_add hPr,Real.sqrt_eq_rpow]; norm_num
  have hnum : 2*A*(n:ℝ)^(1/16:ℝ) ≤ c*Real.sqrt P := calc
    _ ≤ (c*(P:ℝ)^(1/4:ℝ))*(P:ℝ)^(1/4:ℝ) :=
      mul_le_mul (by linarith only [(div_le_iff₀ hc).mp h₂]) hsmall (by positivity) (by positivity)
    _ = _ := by rw [mul_assoc,hsq]
  have hmajor := hErr hX (by omega : 0<P) hn
  have herr : 2*X/Real.sqrt P*(A*(n:ℝ)^(1/16:ℝ)) ≤ c*X := by
    rw [div_mul_eq_mul_div,div_le_iff₀ hs]
    linarith only [mul_le_mul_of_nonneg_left hnum hX.le]
  have he : Real.exp (-1) ≤ Real.exp (-(n:ℝ)/X) :=
    Real.exp_le_exp.mpr ((le_div_iff₀ hX).mpr (by linarith))
  have htarget : 2*c*X ≤ truncatedSingular n P*(n*Real.exp (-(n:ℝ)/X)) := by
    apply le_trans _ (mul_le_mul h₁ (mul_le_mul hhalf he (Real.exp_pos _).le (Nat.cast_nonneg _))
      (by positivity) (by linarith : 0≤truncatedSingular n P))
    unfold c; ring_nf; exact le_rfl
  have hnon := (by linarith : 0≤truncatedSingular n P)
  have hdiff := norm_sub_norm_le (((truncatedSingular n P*(n*Real.exp (-(n:ℝ)/X)) : ℝ):ℂ))
    (majorArcCoefficient X P n)
  rw [norm_sub_rev,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)] at hdiff
  linarith only [htarget,hdiff,hmajor.trans herr]

end GoldbachDensity

namespace GoldbachDensity

open Finset ArithmeticFunction MeasureTheory Complex Set Filter

noncomputable def majorProfile (X : ℝ) (q : ℕ) (b : ℝ) : ℂ :=
  ((moebius q : ℤ):ℂ)/(q.totient:ℂ)/(((X⁻¹:ℝ):ℂ)-2*(Real.pi:ℂ)*(b:ℂ)*I)

theorem phase_den_ne {X : ℝ} (hx : 0 < X) (b : ℝ) :
    ((X⁻¹:ℝ):ℂ)-2*(Real.pi:ℂ)*(b:ℂ)*I ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp [Complex.mul_re,Complex.mul_im] at hre
  exact hx.ne' hre

theorem majorProfile_continuous {X : ℝ} (hx : 0<X) (q : ℕ) : Continuous (majorProfile X q) := by
  unfold majorProfile
  have hd : Continuous (fun b : ℝ => ((X⁻¹:ℝ):ℂ)-2*(Real.pi:ℂ)*(b:ℂ)*I) := by fun_prop
  have hn : Continuous (fun _ : ℝ => ((moebius q:ℤ):ℂ)/(q.totient:ℂ)) := continuous_const
  exact hn.div hd (phase_den_ne hx)

theorem norm_moebius_le (q : ℕ) : ‖((moebius q:ℤ):ℂ)‖ ≤ 1 := by
  rcases moebius_eq_or q with h|h|h <;> norm_num [h]

/-- Uniform lower bound for the totient, using the same positive majorant
as the truncated singular series. -/
theorem totient_ratio_bound {ε : ℝ} (he : 0 < ε) :
    ∃ C : ℝ, 0<C ∧ ∀ q : ℕ, 0<q → (q:ℝ)/(q.totient:ℝ) ≤ C*(q:ℝ)^ε := by
  obtain ⟨C,hC,H⟩ := weighted_euler_bound he
  refine ⟨C,hC,?_⟩
  intro q hq
  have hφ : 0 < (q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hp (p : ℕ) (h : p ∈ q.primeFactors) : 2 ≤ (p:ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors h).two_le
  have hD : (∏ p ∈ q.primeFactors, ((p:ℝ)-1)) ≠ 0 :=
    (Finset.prod_pos fun p h => by linarith [hp p h]).ne'
  have hh : (q.totient:ℝ)*(∏ p ∈ q.primeFactors, (p:ℝ)) =
      (q:ℝ)*(∏ p ∈ q.primeFactors, ((p:ℝ)-1)) := by
    have ho := congrArg (fun a : ℕ => (a:ℝ)) (Nat.totient_mul_prod_primeFactors q)
    push_cast at ho
    convert ho using 2
    apply Finset.prod_congr rfl
    intro p h
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors h).one_le]; simp
  have hsub : q.primeFactors ⊆ primesThrough q := by
    intro p h
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_mem_primeFactors h)),
      Nat.prime_of_mem_primeFactors h⟩
  calc
    _ = ∏ p ∈ q.primeFactors, (p:ℝ)/((p:ℝ)-1) := by
      rw [Finset.prod_div_distrib]; field_simp; linarith only [hh]
    _ ≤ ∏ p ∈ q.primeFactors, (1+Real.sqrt p*|localTerm q p|) := by
      apply Finset.prod_le_prod₀ (fun p h => div_nonneg (Nat.cast_nonneg _) (by linarith [hp p h]))
      intro p h
      have hd : 0 < (p:ℝ)-1 := by linarith [hp p h]
      rw [localTerm,ite_eq_left (Nat.dvd_of_mem_primeFactors h),abs_of_pos (one_div_pos.mpr hd),mul_one_div]
      have hs : 1 ≤ Real.sqrt p := by simpa using Real.sqrt_le_sqrt (show (1:ℝ) ≤ p by linarith [hp p h])
      field_simp; linarith
    _ ≤ _ := (Finset.prod_le_prod_of_subset_of_one_le₀ hsub (fun p _ => by positivity)
      (fun p _ _ => le_add_of_nonneg_right (by positivity))).trans (H q q hq)

set_option maxHeartbeats 1000000 in
/-- The square of the rational denominator is integrable with mass O(X)
on any symmetric real arc. -/
theorem majorProfile_interval_energy {X : ℝ} (hx : 0 < X) {q : ℕ} (hq : 0 < q)
    {h : ℝ} (hh : 0 ≤ h) :
    (∫ b : ℝ in -h..h, ‖majorProfile X q b‖^2) ≤ Real.pi*X/(q.totient:ℝ)^2 := by
  let c := X/(q.totient:ℝ)^2
  have hφ : 0 < (q.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let f := fun b : ℝ => (1+(X*b)^2)⁻¹
  have hdiff (b : ℝ) : HasDerivAt (fun x : ℝ => Real.arctan (X*x)) (X*f b) b := by
    convert (Real.hasDerivAt_arctan (X*b)).comp b ((hasDerivAt_id b).const_mul X) using 1
    · rfl
    · dsimp [f]; ring
  have hf : Continuous f := (continuous_const.add ((continuous_const.mul continuous_id).pow 2)).inv₀
    (fun b => ne_of_gt (by positivity : 0 < 1+(X*b)^2))
  have hpoint (b : ℝ) : ‖majorProfile X q b‖^2 ≤ c*(X*f b) := by
    let z : ℂ := ((X⁻¹:ℝ):ℂ)-2*(Real.pi:ℂ)*(b:ℂ)*I
    have hz : ‖z‖^2 = (X⁻¹)^2 + (2*Real.pi*b)^2 := by
      rw [Complex.sq_norm,Complex.normSq_apply]; simp [z,Complex.mul_re,Complex.mul_im]; ring
    have hπ : 1 ≤ (2*Real.pi)^2 := by nlinarith [Real.pi_gt_three,sq_nonneg (Real.pi-3)]
    have hlow : 1+(X*b)^2 ≤ X^2*‖z‖^2 := by
      rw [hz]; field_simp
      nlinarith only [mul_le_mul_of_nonneg_right hπ (sq_nonneg (b*X))]
    have hpos : 0 < ‖z‖ := norm_pos_iff.mpr (phase_den_ne hx b)
    change ‖((moebius q:ℤ):ℂ)/(q.totient:ℂ)/z‖^2 ≤ _
    rw [norm_div,norm_div,Complex.norm_natCast,div_pow,div_pow]
    have hμ := pow_le_pow_left₀ (norm_nonneg _) (norm_moebius_le q) 2
    norm_num only [one_pow] at hμ
    calc
      _ ≤ (1/(q.totient:ℝ)^2)/‖z‖^2 := by gcongr
      _ ≤ _ := by
        dsimp [c,f]; rw [← div_eq_mul_inv,← mul_div_assoc]
        field_simp
        nlinarith only [hlow]
  have H := intervalIntegral.integral_mono_on (μ := volume) (show -h ≤ h by linarith)
    (((majorProfile_continuous hx q).norm.pow 2).intervalIntegrable ..)
    ((continuous_const.mul (continuous_const.mul hf)).intervalIntegrable ..) (fun b _ => hpoint b)
  change (∫ b in -h..h, ‖majorProfile X q b‖^2) ≤ ∫ b in -h..h, c*(X*f b) at H
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun b => Real.arctan (X*b)) (fun b _ => hdiff b) ((continuous_const.mul hf).intervalIntegrable ..)] at H
  apply H.trans
  have hdiffBound : Real.arctan (X*h)-Real.arctan (X*(-h)) ≤ Real.pi := by
    linarith [Real.arctan_lt_pi_div_two (X*h),Real.neg_pi_div_two_lt_arctan (X*(-h))]
  have bound := mul_le_mul_of_nonneg_left hdiffBound hc
  convert bound using 1; dsimp [c]; ring

end GoldbachDensity

namespace GoldbachDensity

open Finset ArithmeticFunction Complex AddCircle MeasureTheory GoldbachDensityCircle
open scoped Topology Interval

private instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

private noncomputable def arithmeticAmplitude (q : ℕ) : ℂ :=
  ((moebius q : ℤ):ℂ)/(q.totient:ℂ)

private noncomputable def ramanujanMass (n q : ℕ) : ℂ :=
  arithmeticAmplitude q ^ 2 *
    ∑ a ∈ (range q).filter (fun a => a.Coprime q), rationalPhase n q a

private theorem totient_primeSupport {S : Finset ℕ} (hS : ∀ p∈S, Nat.Prime p) :
    (modulusOf S).totient = ∏ p∈S,(p-1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [modulusOf]
  | insert p S hp ih =>
    have hP := hS p (mem_insert_self ..)
    have hS' q hq := hS q (mem_insert_of_mem hq)
    change (∏ q ∈ insert p S,q).totient = _
    rw [prod_insert hp,prod_insert hp,Nat.totient_mul,Nat.totient_prime hP,← ih hS']
    · rfl
    · apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      exact (Nat.coprime_primes hP (hS' q hq)).mpr (fun e => hp (e ▸ hq))

private theorem ramanujanMass_support (n : ℕ) {S : Finset ℕ} (hS : ∀ p∈S, Nat.Prime p) :
    ramanujanMass n (modulusOf S) = (localProduct n S : ℂ) := by
  let q := modulusOf S
  have hF : q.primeFactors = S := Nat.primeFactors_prod hS
  have hsquare : Squarefree q := by
    have hh := binaryShift_squarefree_prod_primeFactors q
    rw [hF] at hh
    exact hh
  have hμ : (((moebius q:ℤ):ℂ))^2 = 1 := by
    exact_mod_cast moebius_sq_eq_one_of_squarefree hsquare
  have hφ : (q.totient:ℂ) = ∏ p∈S, ((p:ℂ)-1) := by
    rw [show q.totient = ∏ p∈S,(p-1) from totient_primeSupport hS,Nat.cast_prod]
    apply prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (hS p hp).one_le,Nat.cast_one]
  have hR : (∑ a ∈ (range q).filter (fun a => a.Coprime q), rationalPhase n q a) =
      ∏ p∈S, ((if p∣n then (p:ℂ) else 0)-1) := squarefree_ramanujan_sum S hS n
  change arithmeticAmplitude q ^ 2 * _ = _
  rw [arithmeticAmplitude,div_pow,hμ,hR,hφ,← Finset.prod_pow]
  unfold localProduct
  push_cast
  rw [one_div_mul_eq_div,← Finset.prod_div_distrib]
  apply prod_congr rfl
  intro p hp
  by_cases h : p∣n
  · simp [localTerm,h,field]
  · simp [localTerm,h]

private theorem ramanujanMass_nonSquarefree (n : ℕ) {q : ℕ} (h : ¬Squarefree q) :
    ramanujanMass n q = 0 := by
  simp [ramanujanMass,arithmeticAmplitude,moebius_eq_zero_of_not_squarefree h]

private theorem sum_moduli_by_support (n P : ℕ) (I : ℕ → ℂ) :
    (∑ q ∈ Icc 1 P, ramanujanMass n q * I q) =
      ∑ s ∈ (primesThrough P).powerset, if modulusOf s ≤ P then
        (localProduct n s : ℂ)*I (modulusOf s) else 0 := by
  classical
  let T := (Icc 1 P).filter Squarefree
  let U := ((primesThrough P).powerset).filter (fun s => modulusOf s ≤ P)
  have hprime {s : Finset ℕ} (hs : s ∈ U) : ∀ p∈s,Nat.Prime p :=
    fun p hp => (mem_filter.mp ((mem_powerset.mp (mem_filter.mp hs).1) hp)).2
  have hF {s : Finset ℕ} (hs : s ∈ U) : (modulusOf s).primeFactors = s :=
    Nat.primeFactors_prod (hprime hs)
  have heq : T = U.image modulusOf := by
    ext q
    constructor
    · intro h
      obtain ⟨hi,hsq⟩ := mem_filter.mp h
      obtain ⟨hql,hqu⟩ := mem_Icc.mp hi
      have he : modulusOf q.primeFactors = q := Nat.prod_primeFactors_of_squarefree hsq
      refine mem_image.mpr ⟨q.primeFactors,mem_filter.mpr ⟨mem_powerset.mpr ?_,by rwa [he]⟩,he⟩
      intro p hp
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_of_mem_primeFactors hp).trans hqu)),
        (Nat.mem_primeFactors.mp hp).1⟩
    · intro h
      obtain ⟨s,hs,rfl⟩ := mem_image.mp h
      have hsqp := binaryShift_squarefree_prod_primeFactors (modulusOf s)
      rw [hF hs] at hsqp
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨prod_pos (fun p hp => (hprime hs p hp).pos),
        (mem_filter.mp hs).2⟩,hsqp⟩
  have hinj : Set.InjOn modulusOf (U:Set (Finset ℕ)) := by
    intro s hs t ht he
    exact (hF hs).symm.trans ((congrArg Nat.primeFactors he).trans (hF ht))
  calc
    _ = ∑ q ∈ T, ramanujanMass n q * I q := by
      symm
      apply sum_subset (filter_subset ..)
      intro q hq hnq
      have hs : ¬Squarefree q := fun h => hnq (mem_filter.mpr ⟨hq,h⟩)
      simp [ramanujanMass_nonSquarefree n hs]
    _ = ∑ s ∈ U, ramanujanMass n (modulusOf s) * I (modulusOf s) := by
      rw [heq,sum_image hinj]
    _ = ∑ s ∈ U, (localProduct n s:ℂ)*I (modulusOf s) :=
      sum_congr rfl (fun s hs => by rw [ramanujanMass_support n (hprime hs)])
    _ = _ := sum_filter ..

private theorem fourier_rationalPhase (q a n : ℕ) :
    fourier (-(n:ℤ)) (arcCenter (q,a) : AddCircle (1:ℝ)) = rationalPhase n q a := by
  rw [fourier_coe_apply,rationalPhase,arcCenter]
  push_cast
  congr 1
  ring

private theorem local_integral_majorProfile (X : ℝ) (P q n : ℕ) :
    (∫ t : ℝ in -(arcWidth X P q)..arcWidth X P q,
      fourier (-(n:ℤ)) (t : AddCircle (1:ℝ)) * majorProfile X q t ^ 2) =
      arithmeticAmplitude q ^ 2 * dampedArcIntegral X P q n := by
  unfold dampedArcIntegral
  dsimp only
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [fourier_coe_apply,majorProfile,arithmeticAmplitude,div_pow]
  push_cast
  have hphase : 2*(Real.pi:ℂ)*I*(-(n:ℂ))*t/1 = -2*(Real.pi:ℂ)*t*n*I := by ring
  rw [hphase]
  ring

/-- Identification of the coefficient of the actual circle model with the
prime-support sum. Coprimality, squarefree multiplicity, the factors of the
totient, and the full archimedean profile are all accounted for. -/
theorem arcModel_coeff_eq_majorArcCoefficient {X : ℝ} (P n : ℕ) (hX : 0<X)
    (hsmall : 2*(P:ℝ)*P<X) (hW : ∀ q, Continuous (majorProfile X q)) :
    fourierCoeff (fun x => (arcModel X P P (majorProfile X) x)^2) (n:ℤ) =
      majorArcCoefficient X P n := by
  rw [arcModel_square_coeff X P P _ hW hX (Nat.cast_nonneg _) hsmall,sum_arcIndices]
  apply Eq.trans _ (sum_moduli_by_support n P (fun q => dampedArcIntegral X P q n))
  apply sum_congr rfl
  intro q _
  simp_rw [fourier_rationalPhase,local_integral_majorProfile]
  rw [← sum_mul,ramanujanMass]
  ring

end GoldbachDensity

namespace GoldbachDensity

open ArithmeticFunction Finset Complex GoldbachDensityCircle

noncomputable def badMass (q : ℕ) (X : ℝ) : ℝ :=
  ∑' n : ℕ, if n.Coprime q then 0 else vonMangoldt n * Real.exp (-(n:ℝ)/X)

theorem damped_norm (X : ℝ) (n : ℕ) :
    ‖mangoldtWeight X n‖ = vonMangoldt n * Real.exp (-(n:ℝ)/X) := by
  rw [mangoldtWeight,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg
    (mul_nonneg vonMangoldt_nonneg (Real.exp_pos _).le)]

theorem badMass_summable (q : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    Summable (fun n : ℕ => if n.Coprime q then 0 else vonMangoldt n * Real.exp (-(n:ℝ)/X)) := by
  apply (mangoldtWeight_summable hX).of_nonneg_of_le
  · intro n; split_ifs <;> positivity [vonMangoldt_nonneg (n:=n)]
  · intro n; rw [damped_norm]; split_ifs <;> first |rfl| positivity [vonMangoldt_nonneg (n:=n)]

/-- Exponential smoothing costs at most two logarithms on prime powers
whose bases divide the modulus. -/
theorem badMass_bound (q : ℕ) [NeZero q] {X : ℝ} (hX : 1 ≤ X) :
    badMass q X ≤ (Real.log q/Real.log 2)*(Real.log X+1) := by
  have hx : 0<X := zero_lt_one.trans_le hX
  let r := Real.exp (-1/X)
  let A := Real.log q/Real.log 2
  let a := fun n : ℕ => if n.Coprime q then (0:ℝ) else vonMangoldt n
  have hA : 0 ≤ A := div_nonneg (Real.log_nonneg (by exact_mod_cast (NeZero.one_le : 1 ≤ q)))
    (Real.log_pos (by norm_num)).le
  have hr : 0 < r := Real.exp_pos _
  have hlt : r < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) hx)
  have hz : ‖r‖ < 1 := by simpa [Real.norm_eq_abs,abs_of_pos hr] using hlt
  have hrpow (n : ℕ) : r^n = Real.exp (-(n:ℝ)/X) := by
    dsimp [r]; rw [← Real.exp_nat_mul]; congr 1; ring
  have ha (n : ℕ) : 0 ≤ a n := by dsimp [a]; split_ifs <;> simp [vonMangoldt_nonneg]
  have hh (n : ℕ) : a n*r^n = if n.Coprime q then 0 else vonMangoldt n * Real.exp (-(n:ℝ)/X) := by
    rw [hrpow]; simp [a,ite_mul]
  have hsum : Summable (fun n : ℕ => a n*r^n) := by
    simp_rw [hh]; exact badMass_summable q hX
  have hgeom := summable_geometric_of_lt_one hr.le hlt
  have hp (n : ℕ) : (∑ k ∈ range (n+1), a k) ≤ A*(Real.log X + n/X) := by
    cases n with
    | zero => simpa [a] using mul_nonneg hA (Real.log_nonneg hX)
    | succ n =>
      have hg := GoldbachDensityProgression.sum_vonMangoldt_not_coprime_le_logs q (n+1) (NeZero.pos _) (by omega)
      rw [Finset.sum_filter] at hg
      have he : 0 < ((n+1:ℕ):ℝ) := by positivity
      have hb := Real.log_le_sub_one_of_pos (div_pos he hx)
      rw [Real.log_div he.ne' hx.ne'] at hb
      apply le_trans _ (mul_le_mul_of_nonneg_left (by linarith only [hb] :
        Real.log ((n+1:ℕ):ℝ) ≤ Real.log X+((n+1:ℕ):ℝ)/X) hA)
      simpa [a,A,ite_not] using hg
  have hconv := hasSum_sum_range_mul_of_summable_norm (f := fun n => a n*r^n)
    (g := fun n => r^n) hsum.norm hgeom.norm
  have hterm (n : ℕ) : (∑ k ∈ range (n+1), a k*r^k*r^(n-k)) ≤
      A*(Real.log X*r^n + (n:ℝ)*r^n/X) := by
    have he : (∑ k ∈ range (n+1), a k*r^k*r^(n-k)) = (∑ k ∈ range (n+1), a k)*r^n := by
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro k hk
      rw [mul_assoc,←pow_add,Nat.add_sub_of_le (by simpa [Nat.lt_succ_iff] using mem_range.mp hk)]
    rw [he]
    apply (mul_le_mul_of_nonneg_right (hp n) (pow_nonneg hr.le _)).trans_eq
    ring
  have hg := hasSum_geometric_of_lt_one hr.le hlt
  have hn := hasSum_coe_mul_geometric_of_norm_lt_one hz
  have hm := ((hg.mul_left (Real.log X)).add (hn.div_const X)).mul_left A
  have hbound := hasSum_le hterm hconv hm
  rw [tsum_geometric_of_lt_one hr.le hlt] at hbound
  have hFinal : r/(1-r) ≤ X := by
    apply (div_le_iff₀ (sub_pos.mpr hlt)).2
    have he := Real.add_one_le_exp (1/X)
    have heq : r*Real.exp (1/X) = 1 := by
      dsimp [r]; rw [← Real.exp_add]; convert Real.exp_zero using 2; ring
    have h := mul_le_mul_of_nonneg_left he hr.le
    rw [heq] at h
    field_simp at h
    linarith
  have hmass : badMass q X = ∑' n, a n*r^n := by simp only [hh,badMass]
  rw [hmass]
  have hden : 0 < 1-r := sub_pos.mpr hlt
  have hdiv : r/(1-r)/X ≤ 1 := (div_le_one hx).2 hFinal
  have hcalc := mul_le_mul_of_nonneg_right hbound hden.le
  calc
    _ = ((∑' n, a n*r^n)*(1-r)⁻¹)*(1-r) := by field_simp
    _ ≤ _ := hcalc
    _ = A*(Real.log X+r/(1-r)/X) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hA

end GoldbachDensity

namespace GoldbachDensity

open Complex Finset ArithmeticFunction DirichletCharacter GoldbachDensityCircle

noncomputable def sequenceTwist {q : ℕ} (χ : DirichletCharacter ℂ q) (w : ℕ → ℂ) : ℂ :=
  ∑' n : ℕ, χ (n:ZMod q) * w n

private theorem unit_damped_summable (w : ℕ → ℂ) (hw : Summable (fun n => ‖w n‖))
    (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1) : Summable (fun n => g n*w n) :=
  ((hw.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => by
    rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hg n))) :
    Summable (fun n => ‖g n*w n‖)).of_norm

theorem sequenceTwist_changeLevel {q d : ℕ} [NeZero q] [NeZero d] (hd : d ∣ q)
    (χ : DirichletCharacter ℂ d) {X : ℝ} (hX : 1 ≤ X) (w : ℕ → ℂ)
    (hw : ∀ n, ‖w n‖ = ‖mangoldtWeight X n‖) :
    ‖sequenceTwist (χ.changeLevel hd) w-sequenceTwist χ w‖ ≤ badMass q X := by
  have hs : Summable (fun n => ‖w n‖) := by simp_rw [hw]; exact mangoldtWeight_summable hX
  have h₁ := unit_damped_summable w hs (fun n => (χ.changeLevel hd) (n:ZMod q))
    (fun _ => DirichletCharacter.norm_le_one ..)
  have h₂ := unit_damped_summable w hs (fun n => χ (n:ZMod d)) (fun _ => χ.norm_le_one _)
  rw [sequenceTwist,sequenceTwist,← h₁.tsum_sub h₂]
  apply (norm_tsum_le_tsum_norm (h₁.sub h₂).norm).trans
  apply (h₁.sub h₂).norm.tsum_le_tsum _ (badMass_summable q hX)
  intro n
  by_cases h : n.Coprime q
  · have he : (χ.changeLevel hd) (n:ZMod q) = χ (n:ZMod d) := by
      simpa using χ.changeLevel_eq_cast_of_dvd' hd (show IsCoprime (n:ℤ) (q:ℤ) from h.cast)
    change ‖(χ.changeLevel hd) (n:ZMod q)*w n-χ (n:ZMod d)*w n‖ ≤ if n.Coprime q then 0 else _
    rw [he, sub_self, norm_zero]; split_ifs; positivity [vonMangoldt_nonneg (n:=n)]
  · have hz := MulChar.map_nonunit (χ.changeLevel hd) (mt (ZMod.isUnit_iff_coprime n q).mp h)
    simp only [hz,zero_mul,zero_sub,norm_neg,norm_mul,ite_eq_right h]
    rw [hw,damped_norm]
    exact mul_le_of_le_one_left (mul_nonneg vonMangoldt_nonneg (Real.exp_pos _).le) (χ.norm_le_one _)

theorem rational_expansion_error (q : ℕ) [NeZero q] (g : ZMod q → ℂ) (hg : ∀ u, ‖g u‖=1)
    {X : ℝ} (hX : 1 ≤ X) (w : ℕ → ℂ) (hw : ∀ n, ‖w n‖=‖mangoldtWeight X n‖) :
    ‖(∑' n : ℕ, g (n:ZMod q)*w n) -
      ∑ χ : DirichletCharacter ℂ q, charCoefficient (fun u => g (u:ZMod q)) χ * sequenceTwist χ w‖
      ≤ badMass q X := by
  classical
  let c := charCoefficient (fun u : (ZMod q)ˣ => g (u:ZMod q))
  have hs : Summable (fun n => ‖w n‖) := by simp_rw [hw]; exact mangoldtWeight_summable hX
  have hsχ (χ : DirichletCharacter ℂ q) := unit_damped_summable w hs (fun n => χ (n:ZMod q)) (fun _ => χ.norm_le_one _)
  have hs' (χ : DirichletCharacter ℂ q) := (hsχ χ).mul_left (c χ)
  have heq : (∑ χ, c χ * sequenceTwist χ w) =
      ∑' n : ℕ, (∑ χ : DirichletCharacter ℂ q, c χ*χ (n:ZMod q))*w n := by
    simp only [sequenceTwist,← tsum_mul_left,← mul_assoc,Finset.sum_mul]
    exact Summable.tsum_finsetSum (fun χ _ => by simpa only [mul_assoc] using hs' χ) |>.symm
  change ‖_ - (∑ χ, c χ*sequenceTwist χ w)‖ ≤ _
  rw [heq]
  have hG := unit_damped_summable w hs (fun n => g (n:ZMod q)) (fun n => (hg _).le)
  have hF : Summable (fun n : ℕ => (∑ χ : DirichletCharacter ℂ q, c χ*χ (n:ZMod q))*w n) := by
    simp only [Finset.sum_mul,mul_assoc]
    exact summable_sum (s:=Finset.univ) fun χ _ => hs' χ
  rw [← hG.tsum_sub hF]
  apply (norm_tsum_le_tsum_norm (hG.sub hF).norm).trans
  apply (hG.sub hF).norm.tsum_le_tsum _ (badMass_summable q hX)
  intro n
  by_cases h : n.Coprime q
  · have hi := charCoefficient_inversion (fun u : (ZMod q)ˣ => g (u:ZMod q)) (ZMod.unitOfCoprime n h)
    simp only [ZMod.coe_unitOfCoprime] at hi
    simp only [c,hi,sub_self,norm_zero,ite_eq_left h,le_refl]
  · have hz (χ : DirichletCharacter ℂ q) : χ (n:ZMod q)=0 :=
      MulChar.map_nonunit _ (mt (ZMod.isUnit_iff_coprime n q).mp h)
    simp only [hz,mul_zero,Finset.sum_const_zero,zero_mul,sub_zero,norm_mul,hg,one_mul,hw,damped_norm,ite_eq_right h,le_refl]

/-- Pass from primitive character estimates to a rational additive twist. -/
theorem additive_from_primitive (q : ℕ) [NeZero q] (g : ZMod q → ℂ) (hg : ∀ u, ‖g u‖=1)
    {X : ℝ} (hX : 1 ≤ X) (w : ℕ → ℂ) (hw : ∀ n, ‖w n‖=‖mangoldtWeight X n‖)
    (M : ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hprim : ∀ (d : ℕ) [NeZero d], d ∣ q → ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
      ‖sequenceTwist χ w-(if χ=1 then M else 0)‖ ≤ B) :
    ‖(∑' n : ℕ, g (n:ZMod q)*w n)-charCoefficient (fun u : (ZMod q)ˣ => g (u:ZMod q)) 1*M‖ ≤
      badMass q X + Real.sqrt q.totient*(badMass q X+B) := by
  let c := charCoefficient (fun u : (ZMod q)ˣ => g (u:ZMod q))
  let L := ∑ χ : DirichletCharacter ℂ q, c χ * sequenceTwist χ w
  have hb : 0 ≤ badMass q X := tsum_nonneg fun n => by split_ifs <;> positivity [vonMangoldt_nonneg (n:=n)]
  have hχ (χ : DirichletCharacter ℂ q) :
      ‖sequenceTwist χ w - (if χ=1 then M else 0)‖ ≤ badMass q X+B := by
    have : NeZero χ.conductor := ⟨(Nat.pos_of_dvd_of_pos χ.conductor_dvd_level (NeZero.pos q)).ne'⟩
    have hc := sequenceTwist_changeLevel χ.conductor_dvd_level χ.primitiveCharacter hX w hw
    rw [χ.changeLevel_primitiveCharacter] at hc
    have h₁ : χ = 1 ↔ χ.primitiveCharacter = 1 := by
      simpa only [χ.changeLevel_primitiveCharacter] using
        (DirichletCharacter.changeLevel_eq_one_iff (χ := χ.primitiveCharacter) χ.conductor_dvd_level)
    simp only [h₁]
    exact (norm_sub_le_norm_sub_add_norm_sub _ (sequenceTwist χ.primitiveCharacter w) _).trans
      (add_le_add hc (hprim _ χ.conductor_dvd_level _ χ.primitiveCharacter_isPrimitive))
  apply (norm_sub_le_norm_sub_add_norm_sub _ L _).trans
  exact add_le_add (rational_expansion_error q g hg hX w hw)
    (additive_twist_error (fun u => hg _) _ M (add_nonneg hb hB) hχ)

end GoldbachDensity

namespace GoldbachDensity

/-- Integer denominator cutoffs for all sufficiently large real scales. -/
theorem exists_arc_cutoffs (P₀ : ℕ) : ∃ X₀ : ℝ, 1 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
    ∃ M Q : ℕ, P₀ ≤ Q ∧ 0 < Q ∧ Q ≤ M ∧ (M:ℝ) ≤ Real.sqrt X ∧
      2*(Q:ℝ)*Q < X ∧ 1/((M:ℝ)+1) ≤ 2/Real.sqrt X ∧ (Q:ℝ)/X ≤ 2/Real.sqrt X ∧
      X ≤ (Q:ℝ)^4 ∧ X/(Q:ℝ) ≤ X^(3/4:ℝ) := by
  refine ⟨max 256 ((P₀:ℝ)^4), (show (1:ℝ) ≤ 256 by norm_num).trans (le_max_left ..), ?_⟩
  intro X hcut
  have hX := (le_max_left 256 ((P₀:ℝ)^4)).trans hcut
  have hP := (le_max_right 256 ((P₀:ℝ)^4)).trans hcut
  have hX' : 0<X := by linarith
  let s := Real.sqrt X
  let t := Real.sqrt s
  let M := ⌊s⌋₊
  let Q := ⌊t⌋₊+1
  have hs : s^2=X := Real.sq_sqrt hX'.le
  have hs₀ : 0<s := Real.sqrt_pos.mpr hX'
  have ht : t^2=s := Real.sq_sqrt hs₀.le
  have ht₀ : 0<t := Real.sqrt_pos.mpr hs₀
  have ht4 : t^4 = X := by calc
    _ = (t^2)^2 := by ring
    _ = _ := by rw [ht,hs]
  have ht4le : 4 ≤ t := by
    apply le_of_pow_le_pow_left₀ (by decide : 4≠0) ht₀.le
    norm_num; linarith only [ht4,hX]
  have hQ : t<(Q:ℝ) := by simpa [Q] using Nat.lt_floor_add_one t
  have hQ' : (Q:ℝ)≤t+1 := by simpa [Q] using add_le_add_left (Nat.floor_le ht₀.le) 1
  have hQ₀ : 0<Q := by dsimp [Q]; omega
  have hQM : Q≤M := Nat.le_floor (hQ'.trans (by nlinarith only [ht,ht4le,sq_nonneg (t-2)]))
  have hPQ : (P₀:ℝ)≤t := by
    apply le_of_pow_le_pow_left₀ (by decide : 4≠0) ht₀.le
    rw [ht4]; exact hP
  have hsmall : 2*(Q:ℝ)*Q < X := by
    have hh : (Q:ℝ)^2 ≤ (t+1)^2 := pow_le_pow_left₀ (by positivity) hQ' 2
    have hh' : 2*(t+1)^2 ≤ 4*s := by nlinarith only [ht,ht4le,sq_nonneg (t-3)]
    have hs4 : 4<s := by nlinarith only [ht,ht4le,sq_nonneg (t-2)]
    nlinarith only [hh,hh',hs,mul_pos hs₀ (sub_pos.mpr hs4)]
  have hsM : s < (M:ℝ)+1 := Nat.lt_floor_add_one s
  have hQle : (Q:ℝ) ≤ s := (Nat.cast_le.mpr hQM).trans (Nat.floor_le hs₀.le)
  have htPow : t = X^(1/4:ℝ) := by
    dsimp [t,s]; rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_mul hX'.le]; norm_num
  have hxPow : X / t = X^(3/4:ℝ) := by
    rw [htPow, show (3/4:ℝ) = 1-1/4 by norm_num, Real.rpow_sub hX',Real.rpow_one]
  refine ⟨M,Q,by exact_mod_cast hPQ.trans hQ.le,hQ₀,hQM,Nat.floor_le hs₀.le,hsmall,?_,?_,?_,?_⟩
  · exact (div_le_div_iff₀ (by positivity) hs₀).2 (by linarith only [hsM,show 0 ≤ (M:ℝ) by positivity])
  · apply (div_le_div_iff₀ hX' hs₀).2
    nlinarith only [mul_le_mul_of_nonneg_right hQle hs₀.le,hs,hX'.le]
  · rw [← ht4]; exact pow_le_pow_left₀ ht₀.le hQ.le 4
  · rw [← hxPow]; exact div_le_div_of_nonneg_left hX'.le ht₀ hQ.le

end GoldbachDensity

namespace GoldbachDensity

open Complex ArithmeticFunction

/-- First saving on the minor arcs, before using the quantitative totient bound. -/
theorem minor_profile_le_ratio {X : ℝ} {q Q : ℕ} {b : ℝ} (hX : 0<X)
    (hq : 0<q) (hQ : 0<Q) (hmin : Q<q ∨ (Q:ℝ)<(q:ℝ)*X*|b|) :
    ‖majorProfile X q b‖ ≤ ((q:ℝ)/(q.totient:ℝ)) * (X/(Q:ℝ)) := by
  let z : ℂ := ((X⁻¹:ℝ):ℂ)-2*(Real.pi:ℂ)*(b:ℂ)*I
  have hzr : z.re = X⁻¹ := by simp [z, Complex.mul_re,Complex.mul_im]
  have hzi : z.im = -(2*Real.pi*b) := by simp [z,Complex.mul_re,Complex.mul_im]
  have hz₁ : X⁻¹ ≤ ‖z‖ := hzr ▸ Complex.re_le_norm z
  have hz₂ : |b| ≤ ‖z‖ := by
    have h := Complex.abs_im_le_norm z
    rw [hzi,abs_neg,abs_mul,abs_of_pos (by positivity : 0<2*Real.pi)] at h
    exact (le_mul_of_one_le_left (abs_nonneg b) (by linarith [Real.pi_gt_three])).trans h
  have hZX : 1 ≤ X*‖z‖ := by
    rw [inv_eq_one_div] at hz₁
    have := (div_le_iff₀ hX).mp hz₁; linarith only [this, mul_comm X ‖z‖]
  have hbound : (Q:ℝ) ≤ (q:ℝ)*X*‖z‖ := by
    rcases hmin with hsmall|hfar
    · have hQq : (Q:ℝ) ≤ q := by exact_mod_cast hsmall.le
      exact hQq.trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hZX (Nat.cast_nonneg q))
    · exact hfar.le.trans (mul_le_mul_of_nonneg_left hz₂ (by positivity))
  have hφ : 0 < (q.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  have hz : 0<‖z‖ := (inv_pos.mpr hX).trans_le hz₁
  have hQ' : 0<(Q:ℝ) := Nat.cast_pos.mpr hQ
  change ‖((moebius q:ℤ):ℂ)/(q.totient:ℂ)/z‖ ≤ _
  rw [norm_div,norm_div,Complex.norm_natCast]
  calc
    _ ≤ (1/(q.totient:ℝ))/‖z‖ := by gcongr; exact norm_moebius_le q
    _ ≤ _ := by field_simp; linarith only [hbound]

/-- A uniform `X^(3/4+ε)` bound for the model at the rational approximation
chosen in the complement of the major arcs. -/
theorem minor_profile_bound {ε : ℝ} (he : 0<ε) : ∃ C : ℝ, 0<C ∧
    ∀ {X : ℝ} {q Q : ℕ} {b : ℝ}, 0<X → 0<q → 0<Q → (q:ℝ) ≤ X →
      X/(Q:ℝ) ≤ X^(3/4:ℝ) → (Q<q ∨ (Q:ℝ)<(q:ℝ)*X*|b|) →
        ‖majorProfile X q b‖ ≤ C*X^(3/4+ε) := by
  obtain ⟨C,hC,H⟩ := totient_ratio_bound he
  refine ⟨C,hC,?_⟩
  intro X q Q b hX hq hQ hqx hsize hminor
  have hr : (q:ℝ)/(q.totient:ℝ) ≤ C*X^ε := (H q hq).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg q) hqx he.le) hC.le)
  calc
    _ ≤ _ := minor_profile_le_ratio hX hq hQ hminor
    _ ≤ (C*X^ε)*X^(3/4:ℝ) := by gcongr
    _ = _ := by rw [Real.rpow_add hX]; ring

end GoldbachDensity

namespace GoldbachDensity

open Complex

/-- The Dirichlet radius controls both the multiplicity-weighted zero sum
and its logarithmic factor uniformly in the rational center. -/
theorem mellin_scale_on_dirichlet_arc {X : ℝ} {q : ℕ} {b : ℝ} (hX : 1≤X) (hq : 0<q)
    (hqs : (q:ℝ) ≤ Real.sqrt X) (hb : |b| ≤ (2/Real.sqrt X)/q) :
    let z : ℂ := ((X⁻¹:ℝ):ℂ)-2*(Real.pi:ℂ)*(b:ℂ)*I
    let T := ‖z‖/z.re
    Real.sqrt q * (‖z‖^(-(1/2):ℝ)*T) ≤ Real.sqrt (1+4*Real.pi) * X^(3/4:ℝ) ∧
      (q:ℝ)*(2+T) ≤ (3+4*Real.pi)*Real.sqrt X := by
  let z : ℂ := ((X⁻¹:ℝ):ℂ)-2*(Real.pi:ℂ)*(b:ℂ)*I
  let T := ‖z‖/z.re
  change Real.sqrt q * (‖z‖^(-(1/2):ℝ)*T) ≤ _ ∧ _*(2+T) ≤ _
  have hX' : 0<X := lt_of_lt_of_le zero_lt_one hX
  have hq' : 0 < (q:ℝ) := Nat.cast_pos.mpr hq
  have hs := Real.sqrt_pos.mpr hX'
  have hz : z.re=X⁻¹ := by simp [z,Complex.mul_re,Complex.mul_im]
  have hz₀ : 0<‖z‖ := (inv_pos.mpr hX').trans_le (hz ▸ Complex.re_le_norm z)
  have hzbound : ‖z‖ ≤ X⁻¹ +2*Real.pi*|b| := by
    apply (norm_sub_le _ _).trans_eq
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX', abs_of_pos Real.pi_pos]
  have hb' : (q:ℝ)*X*|b| ≤ 2*Real.sqrt X := by
    have t := (le_div_iff₀ hs).mp ((le_div_iff₀ hq').mp hb)
    have u := mul_le_mul_of_nonneg_right t hs.le
    calc
      _ = (|b| *(q:ℝ)*Real.sqrt X)*Real.sqrt X := by rw [mul_assoc (|b| *(q:ℝ)), ← sq, Real.sq_sqrt hX'.le]; ring
      _ ≤ _ := u
  have hT : T = X*‖z‖ := by dsimp [T]; rw [hz, div_inv_eq_mul, mul_comm]
  have hqT : (q:ℝ)*T ≤ (1+4*Real.pi)*Real.sqrt X := by
    have H := mul_le_mul_of_nonneg_left hzbound (mul_nonneg hq'.le hX'.le)
    have hI : (q:ℝ)*X*X⁻¹=(q:ℝ) := by field_simp
    have H' := mul_le_mul_of_nonneg_left hb' (show 0≤2*Real.pi by positivity)
    rw [hT]
    nlinarith only [H,hI,H',hqs]
  constructor
  · have hfactor : Real.sqrt q*(‖z‖^(-(1/2):ℝ)*T) = Real.sqrt ((q:ℝ)*T)*Real.sqrt X := by
      rw [hT, Real.rpow_neg hz₀.le, ← Real.sqrt_eq_rpow, Real.sqrt_mul (Nat.cast_nonneg q),
        Real.sqrt_mul hX'.le]
      have ha := Real.sq_sqrt hz₀.le
      have ha' := Real.sq_sqrt hX'.le
      have hS := Real.sqrt_pos.mpr hz₀
      field_simp
      rw [ha,ha']; ring
    rw [hfactor]
    calc
      _ ≤ Real.sqrt ((1+4*Real.pi)*Real.sqrt X)*Real.sqrt X := by gcongr
      _ = _ := by
        rw [Real.sqrt_mul (by positivity : 0≤1+4*Real.pi),mul_assoc]
        congr 1
        simp_rw [Real.sqrt_eq_rpow]
        rw [← Real.rpow_mul hX'.le, ← Real.rpow_add hX']; norm_num
  · nlinarith only [hqT,hqs]

end GoldbachDensity

namespace GoldbachDensity

open Complex Real Filter Set MeasureTheory
open scoped Topology

private theorem gammaLaplace_integrable (k : ℕ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t^k*Real.exp (-(c*t))) (Ioi 0) := by
  simpa only [Real.rpow_one,Real.rpow_natCast,neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (p:=(1:ℝ)) (s:=(k:ℝ)) (b:=c)
      (by linarith [Nat.cast_nonneg (α:=ℝ) k]) zero_lt_one hc)

/-- Complex Laplace scaling of the Gamma integral on the right edge,
obtained by holomorphic continuation in the Laplace parameter. -/
theorem exp_hasMellin_right {s z : ℂ} (hs : s.re=2) (hz : 0<z.re) :
    mellin (fun t : ℝ => Complex.exp (-(z*t))) s = Complex.Gamma s * z^(-s) := by
  let F := fun (w:ℂ) (t:ℝ) => (t:ℂ)^(s-1)*Complex.exp (-(w*t))
  let D := fun (w:ℂ) (t:ℝ) => (t:ℂ)^(s-1)*Complex.exp (-(w*t))*(-(t:ℂ))
  let U := {w : ℂ | 0<w.re}
  have hU : IsOpen U := continuous_re.isOpen_preimage (Ioi (0:ℝ)) isOpen_Ioi
  have hnorm (w : ℂ) (t : ℝ) (ht : 0<t) : ‖F w t‖ = t*Real.exp (-(w.re*t)) := by
    simp only [F,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht,sub_re,hs,one_re,
      Complex.norm_exp,neg_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    norm_num
  have hmeas (w : ℂ) : Measurable (F w) := by dsimp [F]; fun_prop
  have hInt (w : ℂ) (hw : 0<w.re) : IntegrableOn (F w) (Ioi 0) := by
    apply (gammaLaplace_integrable 1 hw).mono' (hmeas w).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht
    simp [hnorm w t ht]
  have hAnal : AnalyticOnNhd ℂ (fun w => ∫ t in Ioi 0, F w t) U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro w hw
    have hw' : 0<w.re := hw
    have hm := (continuous_re.isOpen_preimage (Ioi (w.re/2)) isOpen_Ioi).mem_nhds
      (show w.re/2<w.re by linarith)
    have hd (w:ℂ) (t:ℝ) : HasDerivAt (fun v => F v t) (D w t) w := by
      simpa [F,D,mul_assoc] using ((((hasDerivAt_id w).mul_const (t:ℂ)).neg.cexp).const_mul ((t:ℂ)^(s-1)))
    have hDb : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), ∀ u ∈ {v : ℂ | w.re/2<v.re},
        ‖D u t‖ ≤ t^2*Real.exp (-(w.re/2*t)) := by
      filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht u hu
      change ‖F u t * -(t:ℂ)‖ ≤ _
      rw [norm_mul,hnorm u t ht,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht]
      have he := Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hu.le ht.le))
      calc
        _ = t^2*Real.exp (-(u.re*t)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left he (sq_nonneg _)
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hm
      (Eventually.of_forall (fun v => (hmeas v).aestronglyMeasurable)) (hInt w hw')
      (show AEStronglyMeasurable (D w) (volume.restrict (Ioi 0)) by dsimp [D]; fun_prop)
      hDb (gammaLaplace_integrable 2 (half_pos hw'))
      (Eventually.of_forall (fun t u _ => hd u t))).2.differentiableAt.differentiableWithinAt
  have hRight : AnalyticOnNhd ℂ (fun w : ℂ => Complex.Gamma s*w^(-s)) U := by
    intro w hw
    exact analyticAt_const.mul (analyticAt_id.cpow analyticAt_const (Or.inl hw))
  have hreal {v : ℝ} (hv : 0<v) :
      (∫ t in Ioi (0:ℝ), F (v:ℂ) t) = Complex.Gamma s*(v:ℂ)^(-s) := by
    dsimp only [F]
    rw [integral_cpow_mul_exp_neg_mul_Ioi (by rw [hs]; norm_num) hv,one_div,
      inv_cpow_ofReal_nonneg hv.le,cpow_neg,mul_comm]
  have hfreq : ∃ᶠ w : ℂ in 𝓝[≠] (1:ℂ), (∫ t in Ioi (0:ℝ), F w t) =
      Complex.Gamma s*w^(-s) := by
    have hreal' : ∃ᶠ v : ℝ in 𝓝[≠] (1:ℝ), 0<v :=
      (show ∀ᶠ v : ℝ in 𝓝[≠] (1:ℝ), 0<v from nhdsWithin_le_nhds (lt_mem_nhds zero_lt_one)).frequently
    rw [frequently_iff_seq_forall] at hreal' ⊢
    obtain ⟨v,hv,h⟩ := hreal'
    refine ⟨fun n => (v n : ℂ),?_,fun n => hreal (h n)⟩
    rw [tendsto_nhdsWithin_iff] at hv ⊢
    exact ⟨by simpa using tendsto_ofReal_iff.mpr hv.1,by simpa using hv.2⟩
  exact hAnal.eqOn_of_preconnected_of_frequently_eq hRight (convex_halfSpace_re_gt 0).isPreconnected
    (show (1:ℂ) ∈ U by simp [U]) hfreq hz

end GoldbachDensity

namespace GoldbachDensity

open Complex Real Set Filter MeasureTheory
open scoped Topology

noncomputable def gammaKernel (z s : ℂ) : ℂ := Complex.Gamma s * z^(-s)

theorem gammaKernel_analyticAt {z : ℂ} (hz : 0<z.re) {s : ℂ} (hs : 0<s.re) :
    AnalyticAt ℂ (gammaKernel z) s := by
  have hn : z ≠ 0 := by intro h; rw [h,zero_re] at hz; linarith
  have hGa : AnalyticAt ℂ Complex.Gamma s := by
    apply DifferentiableOn.analyticAt (s:={w : ℂ | 0 < w.re}) _
      ((continuous_re.isOpen_preimage (Ioi (0:ℝ)) isOpen_Ioi).mem_nhds hs)
    intro w hw
    exact (Complex.differentiableAt_Gamma w (by
      intro n h
      have he := congrArg Complex.re h
      simp only [neg_re,natCast_re] at he
      have hx : 0<w.re := hw
      linarith [Nat.cast_nonneg (α:=ℝ) n])).differentiableWithinAt
  have : NeZero z := ⟨hn⟩
  exact hGa.mul (((differentiable_const_cpow_of_neZero z).analyticAt (-s)).comp
    (analyticAt_id.neg))

theorem gammaKernel_damping {s z : ℂ} (hz : 0<z.re) {B : ℝ} (hB : 0 ≤ B)
    (hb : ‖Complex.Gamma s‖ ≤ B * Real.exp (-Real.pi*|s.im|/2)) :
    ‖gammaKernel z s‖ ≤ B * ‖z‖^(-s.re) * Real.exp (-(z.re/‖z‖)*|s.im|) := by
  have hn : z ≠ 0 := by intro h; simp [h] at hz
  have ha := angular_gap_le hz
  have ht : z.arg*s.im ≤ |z.arg| * |s.im| := by rw [← abs_mul]; exact le_abs_self _
  rw [gammaKernel,norm_mul,Complex.norm_cpow_of_ne_zero hn,Complex.neg_re,Complex.neg_im,mul_neg,
    Real.exp_neg,div_inv_eq_mul]
  apply (mul_le_mul_of_nonneg_right hb (by positivity)).trans
  calc
    _ = (B*‖z‖^(-s.re))*Real.exp (-Real.pi*|s.im|/2+z.arg*s.im) := by rw [Real.exp_add]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      linarith only [ht,mul_le_mul_of_nonneg_right ha (abs_nonneg s.im)]

/-- The two rightmost powers in the kernel have uniform exponential
decay even when the Laplace parameter is not real. -/
theorem gammaKernel_strip_bound {z : ℂ} (hz : 0<z.re) :
    ∃ B : ℝ, 0<B ∧ ∀ s : ℂ, 1/4 ≤ s.re → s.re ≤ 2 →
      ‖gammaKernel z s‖ ≤ B*(3+|s.im|)^2*Real.exp (-(z.re/‖z‖)*|s.im|) := by
  obtain ⟨C,hC,h⟩ := gamma_strip_decay
  have hn : 0<‖z‖ := hz.trans_le (Complex.re_le_norm z)
  let b := max (‖z‖^(-(1/4):ℝ)) (‖z‖^(-(2:ℝ)))
  have hb : 0<b := lt_of_lt_of_le (Real.rpow_pos_of_pos hn _) (le_max_left _ _)
  refine ⟨C*b,mul_pos hC hb,?_⟩
  intro s hs₁ hs₂
  have e : ‖z‖^(-s.re) ≤ b := by
    rcases le_total 1 ‖z‖ with hN|hN
    · exact (Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hs₁)).trans (le_max_left _ _)
    · exact (Real.rpow_le_rpow_of_exponent_ge hn hN (neg_le_neg hs₂)).trans (le_max_right _ _)
  apply (gammaKernel_damping hz (by positivity) (h s hs₁ hs₂)).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  calc
    _ ≤ C*(3+|s.im|)^2*b := mul_le_mul_of_nonneg_left e (by positivity)
    _ = _ := by ring

private theorem gamma_poly_decay_int {a : ℝ} (ha : 0<a) :
    Integrable (fun t : ℝ => (3+|t|)^2*Real.exp (-(a*|t|))) := by
  let f := fun t : ℝ => (3+t)^2*Real.exp (-(a*t))
  have h (k : ℕ) := gammaLaplace_integrable k ha
  have hI : IntegrableOn f (Ioi 0) := by
    apply ((((h 0).const_mul 9).add ((h 1).const_mul 6)).add (h 2)).congr
    filter_upwards with t
    simp only [f,Pi.add_apply,pow_zero,pow_one]; ring
  have hpos : IntegrableOn (fun t => f |t|) (Ioi 0) := hI.congr_fun
    (fun t ht => by rw [abs_of_pos (mem_Ioi.mp ht)]) measurableSet_Ioi
  have hneg : IntegrableOn (fun t => f |t|) (Iic 0) := by
    have hc : IntegrableOn (fun t => f |t|) (Ici (-(0:ℝ))) := by
      rw [neg_zero]
      exact (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hpos
    simpa only [abs_neg] using (hc.comp_neg_Iic)
  exact integrableOn_univ.mp (by simpa using hneg.union hpos)

theorem gammaKernel_vertical_integrable {z : ℂ} (hz : 0<z.re) {σ : ℝ} (hσ : 1/4 ≤ σ) (hσ' : σ ≤ 2) :
    Integrable (fun t : ℝ => gammaKernel z ((σ:ℂ)+(t:ℂ)*I)) := by
  obtain ⟨B,hB,hbound⟩ := gammaKernel_strip_bound hz
  have hpos : 0 < z.re/‖z‖ := div_pos hz (hz.trans_le (Complex.re_le_norm z))
  have hInt := (gamma_poly_decay_int hpos).const_mul B
  apply hInt.mono'
  · apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (gammaKernel_analyticAt hz (s:=((σ:ℂ)+(t:ℂ)*I)) (by simp; linarith)).continuousAt.comp
      (f:=fun u : ℝ => (σ:ℂ)+(u:ℂ)*I) (by fun_prop)
  · refine Eventually.of_forall fun t => ?_
    simpa [mul_assoc,neg_mul] using hbound ((σ:ℂ)+(t:ℂ)*I) (by simpa using hσ) (by simpa using hσ')

end GoldbachDensity

namespace GoldbachDensity

open Complex Set MeasureTheory Filter Finset ArithmeticFunction DirichletCharacter

noncomputable def smoothedTwist {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (χ (n : ZMod q)*(vonMangoldt n : ℂ))*Complex.exp (-(z*n))

noncomputable def vertical (σ t : ℝ) : ℂ := (σ:ℂ)+(t:ℂ)*I

private theorem exp_inversion {z : ℂ} (hz : 0<z.re) {v : ℝ} (hv : 0<v) :
    mellinInv 2 (gammaKernel z) v = Complex.exp (-(z*v)) := by
  let f := fun t : ℝ => Complex.exp (-(z*t))
  have hr (t : ℝ) : mellin f (vertical 2 t) = gammaKernel z (vertical 2 t) :=
    exp_hasMellin_right (by simp [vertical]) hz
  have hInt : MellinConvergent f 2 := by
    apply (gammaLaplace_integrable 1 hz).mono'
    · dsimp [f]; fun_prop
    filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=(0:ℝ)))] with t ht
    norm_num [f,smul_eq_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht,Complex.norm_exp]
    rw [abs_of_pos ht]
  have hvInt : VerticalIntegrable (mellin f) 2 := by
    change Integrable (fun t : ℝ => mellin f (vertical 2 t))
    simp_rw [hr]
    exact gammaKernel_vertical_integrable hz (by norm_num) (by norm_num)
  have hh := mellinInv_mellin_eq 2 f hv hInt hvInt (by dsimp [f]; fun_prop)
  unfold mellinInv at hh ⊢
  simpa only [show ∀ t : ℝ, mellin f (((2:ℝ):ℂ)+(t:ℂ)*I) = gammaKernel z (((2:ℝ):ℂ)+(t:ℂ)*I) from hr] using hh

theorem smoothedTwist_eq_right_integral {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {z : ℂ} (hz : 0<z.re) :
    smoothedTwist χ z = (1/(2*Real.pi):ℝ) • ∫ t : ℝ,
      (-logDeriv χ.LFunction (vertical 2 t)) * gammaKernel z (vertical 2 t) := by
  let a := fun n : ℕ => χ (n : ZMod q)*(vonMangoldt n : ℂ)
  have ha₀ : a 0 = 0 := by simp [a]
  have ha : LSeriesSummable a 2 := LSeriesSummable_twist_vonMangoldt χ (by norm_num)
  let F := fun (n : ℕ) (t : ℝ) => LSeries.term a (vertical 2 t) n * gammaKernel z (vertical 2 t)
  let b := fun n : ℕ => ‖LSeries.term a 2 n‖
  have hV := gammaKernel_vertical_integrable hz (σ:=2) (by norm_num) (by norm_num)
  have hnorm (n : ℕ) (t : ℝ) : ‖F n t‖ = b n * ‖gammaKernel z (vertical 2 t)‖ := by
    simp [F,b,LSeries.norm_term_eq,vertical]
  have hmeas (n : ℕ) : AEStronglyMeasurable (F n) := by
    apply AEStronglyMeasurable.mul _ hV.aestronglyMeasurable
    apply Measurable.aestronglyMeasurable
    simp only [LSeries.term_def₀ ha₀,vertical]
    fun_prop
  have hi (n : ℕ) : Integrable (F n) := by
    apply (hV.norm.const_mul (b n)).mono' (hmeas n)
    exact Eventually.of_forall fun t => (hnorm n t).le
  have hs : Summable (fun n => ∫ t : ℝ, ‖F n t‖) := by
    simp_rw [hnorm, integral_const_mul]
    exact ha.norm.mul_right _
  have hsum (t : ℝ) : (∑' n, F n t) = (-logDeriv χ.LFunction (vertical 2 t))*gammaKernel z (vertical 2 t) := by
    rw [show (∑' n, F n t) = _ from tsum_mul_right]
    change LSeries a (vertical 2 t) * _ = _
    have ht : 1 < (vertical 2 t).re := by norm_num [vertical]
    rw [logDeriv_apply,deriv_LFunction_eq_deriv_LSeries χ ht, LFunction_eq_LSeries χ ht,
      ← neg_div,← LSeries_twist_vonMangoldt_eq χ ht]
    rfl
  have hsingle (n : ℕ) : (1/(2*Real.pi):ℝ) • (∫ t : ℝ, F n t) = a n*Complex.exp (-(z*n)) := by
    rcases eq_or_ne n 0 with rfl|hn
    · simp [F,ha₀]
    have hp : 0 < (n:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have he (t : ℝ) : F n t = a n * (((n:ℝ):ℂ)^(-vertical 2 t) * gammaKernel z (vertical 2 t)) := by
      simp only [F,LSeries.term_def₀ ha₀,Complex.ofReal_natCast,Complex.cpow_neg]
      ring
    have h := exp_inversion hz hp
    rw [← ofReal_natCast,← h]
    unfold mellinInv
    simp_rw [he]
    rw [integral_const_mul,mul_smul_comm]
    rfl
  have h := (hasSum_integral_of_summable_integral_norm hi hs).const_smul (1/(2*Real.pi):ℝ)
  simp_rw [hsingle,hsum] at h
  exact h.tsum_eq

end GoldbachDensity

namespace GoldbachDensity

open Complex Filter Set DirichletCharacter GoldbachDensityProgression
open scoped Classical Topology

private theorem neg_logDeriv_zero_principal_part {f : ℂ → ℂ} {ρ : ℂ}
    (hf : AnalyticAt ℂ f ρ) (ho : analyticOrderAt f ρ ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧ (fun z => -logDeriv f z) =ᶠ[𝓝[≠] ρ]
      fun z => g z + (-(analyticOrderNatAt f ρ : ℂ)) * (z-ρ)⁻¹ := by
  obtain ⟨g,hg,he⟩ := logDeriv_principal_part hf ho
  refine ⟨fun z => -g z, hg.neg, ?_⟩
  filter_upwards [he] with z hz
  rw [hz, div_eq_mul_inv]
  ring

private theorem neg_logDeriv_principal_character_pole (q : ℕ) [NeZero q] :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 1 ∧
      (fun z => -logDeriv (LFunction (1 : DirichletCharacter ℂ q)) z) =ᶠ[𝓝[≠] (1 : ℂ)]
        fun z => g z + 1 * (z-1)⁻¹ := by
  let F := LFunctionTrivChar₁ q
  have ha : AnalyticAt ℂ F 1 := (differentiable_LFunctionTrivChar₁ q).analyticAt 1
  have hn : F 1 ≠ 0 := LFunctionTrivChar₁_apply_one_ne_zero q
  refine ⟨fun z => -logDeriv F z, (ha.deriv.div ha hn).neg, ?_⟩
  filter_upwards [(ha.continuousAt.eventually_ne hn).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hF hz
  have hz' : z ≠ 1 := hz
  have he : F z = (z-1) * LFunction (1 : DirichletCharacter ℂ q) z :=
    Function.update_of_ne hz' _ _
  have hL : LFunction (1 : DirichletCharacter ℂ q) z ≠ 0 := right_ne_zero_of_mul (he ▸ hF)
  simp only [logDeriv_apply, F, deriv_LFunctionTrivChar₁_apply_of_ne_one q hz', one_mul]
  rw [show LFunctionTrivChar₁ q z = _ from he]
  change _ = -(((z-1) * deriv (LFunction (1 : DirichletCharacter ℂ q)) z +
    LFunction (1 : DirichletCharacter ℂ q) z) / _) + _
  field_simp [sub_ne_zero.mpr hz', hL]
  ring

/-- Exact Perron residue identity throughout a positive-real-part rectangle
straddling the point 1. It covers principal and nonprincipal characters of any modulus.
`Z` consists of the zeros in the closed rectangle away from 1, and all
these zeros are assumed strictly inside the rectangle. -/
theorem character_weighted_rectangle {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (W : ℂ → ℂ) (hW : ∀ s : ℂ, 0 < s.re → AnalyticAt ℂ W s) {a b u v : ℝ} (ha : 0 < a) (ha1 : a < 1) (hb1 : 1 < b)
    (hu : u < 0) (hv : 0 < v) (Z : Finset ℂ)
    (hZ : ∀ z : ℂ, z ∈ Z ↔ z ∈ Icc a b ×ℂ Icc u v ∧ z ≠ 1 ∧ χ.LFunction z = 0)
    (hint : ∀ z ∈ Z, a < z.re ∧ z.re < b ∧ u < z.im ∧ z.im < v) :
    rectangleBoundary a b u v (fun z => -logDeriv χ.LFunction z * W z) =
      (2 * Real.pi * I) * ((if χ = 1 then W 1 else 0) -
        ∑ z ∈ Z, (analyticOrderNatAt χ.LFunction z : ℂ) * W z) := by
  classical
  let P := if χ = 1 then insert (1 : ℂ) Z else Z
  let r (z : ℂ) := if χ = 1 ∧ z = 1 then W 1
                    else -(analyticOrderNatAt χ.LFunction z : ℂ) * W z
  have memP (z : ℂ) : z ∈ P ↔ (χ = 1 ∧ z = 1) ∨ z ∈ Z := by
    by_cases hχ : χ = 1 <;> simp [P,hχ]
  have hane (z : ℂ) (hz : z ≠ 1 ∨ χ ≠ 1) : AnalyticAt ℂ χ.LFunction z := by
    rcases hz with h | h
    · have han : AnalyticOnNhd ℂ χ.LFunction ({1}ᶜ : Set ℂ) :=
        (show DifferentiableOn ℂ χ.LFunction ({1}ᶜ : Set ℂ) from fun w hw =>
          (differentiableAt_LFunction χ w (.inl hw)).differentiableWithinAt).analyticOnNhd
          isOpen_compl_singleton
      exact han z h
    · exact (differentiable_LFunction h).analyticAt z
  have hrect := rectangle_residues_of_local_principal_parts a b u v
    (ha1.trans hb1).le (hu.trans hv).le (fun z => -logDeriv χ.LFunction z * W z) P r
  have hgeom (z : ℂ) (hz : z ∈ P) : a < z.re ∧ z.re < b ∧ u < z.im ∧ z.im < v := by
    rcases (memP z).mp hz with ⟨_,rfl⟩ | h
    · exact ⟨ha1,hb1,hu,hv⟩
    · exact hint z h
  have he := hrect hgeom (by
    intro z hz hn
    have hns : ¬(χ = 1 ∧ z = 1) := fun h => hn ((memP z).2 (.inl h))
    have hne : z ≠ 1 ∨ χ ≠ 1 := by tauto
    have hnL : χ.LFunction z ≠ 0 := by
      intro h
      by_cases h1 : z = 1
      · subst z
        exact LFunction_ne_zero_of_one_le_re χ (.inl (by tauto)) (by simp) h
      · exact hn ((memP z).2 <| .inr <| (hZ z).2 ⟨hz,h1,h⟩)
    have hL := hane z hne
    exact ((hL.deriv.div hL hnL).neg.mul (hW z (ha.trans_le hz.1.1))).differentiableAt) (by
    intro z hz
    have hw := hW z (ha.trans (hgeom z hz).1)
    rcases (memP z).1 hz with ⟨hχ,rfl⟩ | h
    · subst χ
      simpa [r] using analytic_weight_principal_part hw (neg_logDeriv_principal_character_pole q)
    · obtain ⟨_,h1,hL⟩ := (hZ z).1 h
      have ho : analyticOrderAt χ.LFunction z ≠ ⊤ := by
        intro ho
        have hp := positive_multiplicity_of_character_zero χ h1 hL
        simp [analyticOrderNatAt,ho] at hp
      simpa [r,h1] using analytic_weight_principal_part hw
        (neg_logDeriv_zero_principal_part (hane z (.inl h1)) ho))
  rw [he]
  congr 1
  have hn1 : (1 : ℂ) ∉ Z := by intro h; exact ((hZ 1).1 h).2.1 rfl
  have hsum : ∑ z ∈ Z, r z = - ∑ z ∈ Z, (analyticOrderNatAt χ.LFunction z : ℂ) * W z := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun z hz => by simp [r,((hZ z).1 hz).2.1]
  by_cases hχ : χ = 1
  · rw [show P = insert (1 : ℂ) Z from ite_eq_left hχ, Finset.sum_insert hn1, hsum]
    simp [r,hχ,sub_eq_add_neg]
  · simp [P,hχ,hsum]

/-- Under GRH, avoiding the zero ordinates on the two horizontal sides suffices.
The finite sum ranges precisely over the nontrivial zeros between those sides. -/
theorem character_weighted_rectangle_of_GRH {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (W : ℂ → ℂ) (hW : ∀ s : ℂ, 0 < s.re → AnalyticAt ℂ W s) {a b u v : ℝ} (ha : 0 < a) (ha' : a < 1/2) (hb : 1 < b)
    (hu : u < 0) (hv : 0 < v)
    (hGRH : ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 → z.re = 1/2)
    (hsafe : ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 → z.im ≠ u ∧ z.im ≠ v) :
    ∃ Z : Finset ℂ,
      (∀ z : ℂ, z ∈ Z ↔ 0 < z.re ∧ z.re < 1 ∧ u < z.im ∧ z.im < v ∧ χ.LFunction z = 0) ∧
      rectangleBoundary a b u v (fun z => -logDeriv χ.LFunction z * W z) =
        (2 * Real.pi * I) * ((if χ = 1 then W 1 else 0) -
          ∑ z ∈ Z, (analyticOrderNatAt χ.LFunction z : ℂ) * W z) := by
  classical
  let K := Icc a b ×ℂ Icc u v
  have hfin := finite_character_zeros_on_compact χ
    (show IsCompact K from isCompact_Icc.reProdIm isCompact_Icc)
  let Z := hfin.toFinset
  have hZ (z : ℂ) : z ∈ Z ↔ z ∈ Icc a b ×ℂ Icc u v ∧ z ≠ 1 ∧ χ.LFunction z = 0 :=
    hfin.mem_toFinset
  have hcrit (z : ℂ) (hz : z ∈ Z) :
      0 < z.re ∧ z.re < 1 ∧ u < z.im ∧ z.im < v ∧ χ.LFunction z = 0 := by
    obtain ⟨hbox, hne, hzero⟩ := (hZ z).1 hz
    have h₀ := ha.trans_le hbox.1.1
    have h₁ : z.re < 1 := lt_of_not_ge fun h =>
      LFunction_ne_zero_of_one_le_re χ (.inr hne) h hzero
    obtain ⟨hs₁,hs₂⟩ := hsafe z h₀ h₁ hzero
    exact ⟨h₀,h₁,lt_of_le_of_ne hbox.2.1 hs₁.symm,lt_of_le_of_ne hbox.2.2 hs₂,hzero⟩
  refine ⟨Z,fun z => ⟨hcrit z, ?_⟩, character_weighted_rectangle χ W hW ha
    (by linarith) hb hu hv Z hZ ?_⟩
  · rintro ⟨h₀,h₁,hu',hv',hzero⟩
    have hline := hGRH z h₀ h₁ hzero
    have hn : z ≠ 1 := by intro h; simp [h] at h₁
    exact (hZ z).2 ⟨⟨⟨by linarith,by linarith⟩,hu'.le,hv'.le⟩,hn,hzero⟩
  · intro z hz
    obtain ⟨h₀,h₁,hu',hv',hzero⟩ := hcrit z hz
    have hline := hGRH z h₀ h₁ hzero
    exact ⟨by linarith,by linarith,hu',hv'⟩


end GoldbachDensity

namespace GoldbachDensity

open Complex Set MeasureTheory Filter GoldbachDensityProgression
open scoped Topology Interval

theorem laplace_log_damp {q T t : ℝ} (hq : 1 ≤ q) (hT : 1 ≤ T) (ht : 0 ≤ t) :
    Real.log (q*(2+t))*Real.exp (-t/T) ≤
      (Real.log (q*(2+T))+2)*Real.exp (-t/(2*T)) := by
  let L := Real.log (q*(2+T))
  let u := t/(2*T)
  have hT₀ : 0<T := by linarith
  have hq₀ : 0<q := by linarith
  have hL : 0 ≤ L := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq (by linarith))
  have hlog : Real.log (q*(2+t)) ≤ L+t/T := by
    have h :(2+t) ≤ (2+T)*Real.exp (t/T) := by
      apply le_trans _ (mul_le_mul_of_nonneg_left (Real.add_one_le_exp (t/T)) (by linarith))
      field_simp
      nlinarith only [sq_nonneg T,ht]
    have h' := Real.log_le_log (by positivity : 0 < q*(2+t)) (mul_le_mul_of_nonneg_left h hq₀.le)
    rwa [← mul_assoc,Real.log_mul (by positivity) (Real.exp_pos _).ne',Real.log_exp] at h'
  apply (mul_le_mul_of_nonneg_right hlog (Real.exp_pos _).le).trans
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have h2u : t/T = 2*u := by dsimp [u]; ring
  rw [neg_div,h2u,show -(2*u) = -u + -u by ring,Real.exp_add,← mul_assoc,neg_div]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  rw [Real.exp_neg,← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).2
  have he := Real.add_one_le_exp u
  nlinarith only [mul_nonneg hL (show 0 ≤ Real.exp u - 1 by linarith),he]

theorem damped_abs_mass {T : ℝ} (hT : 0<T) :
    (∫ t : ℝ, Real.exp (-|t|/(2*T))) = 4*T := by
  let a := -(1/(2*T))
  have ha : a<0 := neg_neg_of_pos (by positivity : 0<1/(2*T))
  change (∫ t : ℝ, (fun u : ℝ => Real.exp (-u/(2*T))) |t|) = _
  rw [integral_comp_abs (f:=fun u : ℝ => Real.exp (-u/(2*T)))]
  have he (u : ℝ) : -u/(2*T) = a*u := by dsimp [a]; ring
  simp_rw [he]
  rw [integral_exp_mul_Ioi ha 0]
  simp [a]
  ring

noncomputable def twistIntegrand {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (z s : ℂ) : ℂ :=
  -logDeriv χ.LFunction s * gammaKernel z s

noncomputable def leftGammaConst :=
  contourLogDerivBound*(Real.Gamma (1/4)/Real.Gamma (1/2)*Real.sqrt (2*Real.pi))

theorem gamma_left_edge {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive)
    (hGRH : ∀ s : ℂ, 0 < s.re → s.re < 1 → χ.LFunction s = 0 → s.re=1/2)
    {z : ℂ} (hz : 0<z.re) (hz₁ : ‖z‖≤1) {u v : ℝ} (huv : u≤v) :
    let T := ‖z‖/z.re
    ‖∫ t : ℝ in u..v, twistIntegrand χ z (vertical (1/4) t)‖ ≤
      4*leftGammaConst*(‖z‖^(-(1/2):ℝ)*T)*(Real.log ((q:ℝ)*(2+T))+2) := by
  let T := ‖z‖/z.re
  let L := Real.log ((q:ℝ)*(2+T))
  let B := Real.Gamma (1/4)/Real.Gamma (1/2)*Real.sqrt (2*Real.pi)
  have hq : 1 ≤ (q:ℝ) := by exact_mod_cast q.pos_of_neZero
  have hT : 1 ≤ T := (one_le_div hz).2 (Complex.re_le_norm z)
  have hT₀ : 0<T := by linarith
  have hL : 0≤L := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq (by linarith))
  have hN : 0<‖z‖ := hz.trans_le (Complex.re_le_norm z)
  have hB : 0 ≤ B := by
    dsimp [B]; positivity [Real.Gamma_pos_of_pos (by norm_num : 0 < (1/4:ℝ)),
      Real.Gamma_pos_of_pos (by norm_num : 0 < (1/2:ℝ))]
  let M := leftGammaConst * ‖z‖^(-(1/2):ℝ) * (L+2)
  have hC : 0 ≤ leftGammaConst := mul_nonneg contourLogDerivBound_pos.le hB
  have hM : 0≤M := by dsimp [M]; positivity
  have hb (t : ℝ) : ‖twistIntegrand χ z (vertical (1/4) t)‖ ≤ M*Real.exp (-|t|/(2*T)) := by
    let s := vertical (1/4) t
    have hre : s.re=1/4 := by simp [s,vertical]
    have him : s.im=t := by simp [s,vertical]
    have hv := gammaKernel_damping hz hB (gamma_quarter_decay hre)
    have hzT : z.re/‖z‖ = T⁻¹ := by simp [T]
    rw [hre,him,hzT,show -T⁻¹*|t| = -|t|/T by ring] at hv
    have hh := primitive_logDeriv_left χ hprim s hre hGRH
    rw [him] at hh
    have hNorm : ‖z‖^(-(1/4):ℝ) ≤ ‖z‖^(-(1/2):ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hN hz₁ (by norm_num)
    have hlog : 0≤Real.log ((q:ℝ)*(2+|t|)) := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq
      (by linarith [abs_nonneg t]))
    have hK := hv.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNorm hB) (Real.exp_pos _).le)
    change ‖-logDeriv χ.LFunction s * gammaKernel z s‖ ≤ _
    rw [norm_mul,norm_neg]
    apply (mul_le_mul hh hK (norm_nonneg _) (mul_nonneg contourLogDerivBound_pos.le hlog)).trans
    calc
      _ = (leftGammaConst*‖z‖^(-(1/2):ℝ))*
          (Real.log ((q:ℝ)*(2+|t|))*Real.exp (-|t|/T)) := by dsimp only [leftGammaConst,B]; ring
      _ ≤ _ := by
        simpa only [M,L,mul_assoc] using mul_le_mul_of_nonneg_left
          (laplace_log_damp hq hT (abs_nonneg t)) (mul_nonneg hC (Real.rpow_nonneg (norm_nonneg _) _))
  have hmass := damped_abs_mass hT₀
  have hInt : Integrable (fun t : ℝ => Real.exp (-|t|/(2*T))) := by
    by_contra h
    rw [integral_undef h] at hmass
    linarith
  have heq := intervalIntegral.norm_integral_le_of_norm_le huv
    (Eventually.of_forall (fun t _ => hb t)) ((hInt.const_mul M).intervalIntegrable)
  apply heq.trans
  rw [intervalIntegral.integral_of_le huv]
  apply (setIntegral_le_integral (hInt.const_mul M) (Eventually.of_forall (fun t => by positivity))).trans_eq
  rw [integral_const_mul,hmass]
  dsimp only [M,T,L]
  ring

end GoldbachDensity

namespace GoldbachDensity

open Complex Real Set Filter MeasureTheory GoldbachDensityProgression
open scoped Topology Interval

noncomputable def gammaHorizontal {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (z : ℂ) (t : ℝ) : ℂ :=
  ∫ σ : ℝ in (1/4)..2, twistIntegrand χ z (vertical σ t)

theorem gamma_good_horizontals {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive)
    (hGRH : ∀ s : ℂ, 0<s.re → s.re<1 → χ.LFunction s=0 → s.re=1/2) {z : ℂ} (hz : 0<z.re) :
    ∃ u v : ℕ → ℝ, Tendsto u atTop atBot ∧ Tendsto v atTop atTop ∧
      (∀ n, u n<0 ∧ 0<v n ∧ ∀ ρ : ℂ, 0<ρ.re → ρ.re<1 → χ.LFunction ρ=0 →
        ρ.im≠u n ∧ ρ.im≠v n) ∧
      Tendsto (fun n => ‖gammaHorizontal χ z (u n)‖) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖gammaHorizontal χ z (v n)‖) atTop (𝓝 0) := by
  classical
  let T (n : ℕ) := (n:ℝ)+2
  let c := z.re/‖z‖
  let D : ℝ := 10/Real.log (23/22)
  let K := contourLogDerivBound
  have hc : 0<c := div_pos hz (hz.trans_le (Complex.re_le_norm z))
  have hD : 0≤D := by dsimp [D]; positivity [Real.log_pos (by norm_num : (1:ℝ)<23/22)]
  have hK : 0≤K := contourLogDerivBound_pos.le
  have hq : 1 ≤ (q:ℝ) := by exact_mod_cast q.pos_of_neZero
  have hT (n : ℕ) : 2≤T n := by dsimp [T]; linarith [Nat.cast_nonneg (α:=ℝ) n]
  choose u hu v hv hsafe hhor _ using fun n => primitive_good_contour χ hprim (T n) (hT n) hGRH
  have hTlim : Tendsto T atTop atTop := tendsto_atTop_mono (fun n => by dsimp [T]; linarith)
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hu₀ (n : ℕ) : u n<0 := by linarith [(hu n).2,hT n]
  have hv₀ (n : ℕ) : 0<v n := by linarith [(hv n).1,hT n]
  refine ⟨u,v,tendsto_atBot_mono (fun n => (hu n).2) (tendsto_neg_atBot_iff.mpr hTlim),
    tendsto_atTop_mono (fun n => (hv n).1) hTlim,fun n => ⟨hu₀ n,hv₀ n,hsafe n⟩,?_⟩
  obtain ⟨B,hB,hker⟩ := gammaKernel_strip_bound hz
  let M := 2*(K*(4+3*D)*(3*(q:ℝ))^2)*(9*B)
  have hM : 0≤M := by dsimp [M]; positivity
  have hedge (n : ℕ) (t : ℝ) (hte : t=u n ∨ t=v n) :
      ‖gammaHorizontal χ z t‖ ≤ M*((T n)^4*Real.exp (-c*T n)) := by
    let R := T n
    let Y := Real.log ((q:ℝ)*(2+(R+1)))
    let A := K*(4+3*D)*(3*(q:ℝ))^2
    have hR : 2≤R := hT n
    have hR₀ : 0≤R := by linarith
    have ht : R≤|t| ∧ |t|≤R+1 := by
      rcases hte with rfl|rfl
      · rw [abs_of_neg (hu₀ n)]; exact ⟨by linarith [(hu n).2],by linarith [(hu n).1]⟩
      · rw [abs_of_pos (hv₀ n)]; exact hv n
    have hY : 0≤Y := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq (by linarith))
    have hQ : 1≤(3*(q:ℝ))*R := by nlinarith [mul_nonneg (sub_nonneg.mpr hq) hR₀]
    have hY' : Y≤(3*(q:ℝ))*R := by
      have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < (q:ℝ)*(2+(R+1)))
      dsimp only [Y]
      nlinarith [mul_nonneg (show 0 ≤ (q:ℝ) by positivity) (show 0≤2*R-3 by linarith)]
    have hfac : 1+3*(D*Y+1) ≤ (4+3*D)*((3*(q:ℝ))*R) := by
      nlinarith [mul_le_mul_of_nonneg_left hY' hD]
    have hld : K*(1+3*(D*Y+1))*Y ≤ A*R^2 := by
      have h := mul_le_mul (mul_le_mul_of_nonneg_left hfac hK) hY' hY (by positivity)
      exact h.trans_eq (by dsimp [A]; ring)
    have hpol : (3+|t|)^2 ≤ 9*R^2 := by
      have h := pow_le_pow_left₀ (by positivity : 0≤3+|t|) (by linarith [ht.2] : 3+|t|≤3*R) 2
      linarith
    have hep : Real.exp (-c*|t|) ≤ Real.exp (-c*R) := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left ht.1 (neg_nonpos.mpr hc.le))
    have hk : B*(3+|t|)^2*Real.exp (-c*|t|) ≤ (9*B)*R^2*Real.exp (-c*R) := by
      apply (mul_le_mul (mul_le_mul_of_nonneg_left hpol hB.le) hep (Real.exp_pos _).le (by positivity)).trans_eq
      ring
    have hb (σ : ℝ) (hσ : σ ∈ Ι (1/4:ℝ) 2) :
        ‖twistIntegrand χ z (vertical σ t)‖ ≤ (A*R^2)*((9*B)*R^2*Real.exp (-c*R)) := by
      rw [uIoc_of_le (by norm_num)] at hσ
      let s := vertical σ t
      have hs : s.re=σ := by simp [s,vertical]
      have hs' : s.im=t := by simp [s,vertical]
      have hh := hhor n s (hs ▸ hσ.1.le) (hs ▸ hσ.2) (hs' ▸ hte)
      have hb' := hker s (hs ▸ hσ.1.le) (hs ▸ hσ.2)
      rw [hs'] at hb'
      change ‖-logDeriv χ.LFunction s*gammaKernel z s‖ ≤ _
      rw [norm_mul,norm_neg]
      exact mul_le_mul (hh.trans hld) (hb'.trans hk) (norm_nonneg _) (by dsimp [A]; positivity)
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const hb
    change ‖∫ σ : ℝ in (1/4)..2, twistIntegrand χ z (vertical σ t)‖ ≤ _
    apply hh.trans
    norm_num
    have hA : 0≤A := by dsimp [A]; positivity
    change _ ≤ (2*A*(9*B))*(R^4*Real.exp (-(c*R)))
    nlinarith only [mul_nonneg (mul_nonneg (mul_nonneg hA hB.le) (pow_nonneg hR₀ 4)) (Real.exp_pos (-(c*R))).le]
  have hlim : Tendsto (fun n => M*((T n)^4*Real.exp (-c*T n))) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 4 c hc).comp hTlim).const_mul M
    simpa only [Function.comp_def,Real.rpow_ofNat,mul_zero] using h
  exact ⟨squeeze_zero (fun _ => norm_nonneg _) (fun n => hedge n (u n) (.inl rfl)) hlim,
    squeeze_zero (fun _ => norm_nonneg _) (fun n => hedge n (v n) (.inr rfl)) hlim⟩

end GoldbachDensity

namespace GoldbachDensity

open Complex Real Filter Set MeasureTheory GoldbachDensityProgression
open scoped Topology Interval

private theorem twistIntegrand_integrable_right {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {z : ℂ} (hz : 0<z.re) : Integrable (fun t : ℝ => twistIntegrand χ z (vertical 2 t)) := by
  have hG := gammaKernel_vertical_integrable hz (σ:=2) (by norm_num) (by norm_num)
  have hm (t : ℝ) : twistIntegrand χ z (vertical 2 t) =
      negLogL χ (verticalPoint 2 t) * gammaKernel z (vertical 2 t) := by
    simp [twistIntegrand,negLogL,logDeriv_apply,vertical,verticalPoint,neg_div]
  simp_rw [hm]
  apply (hG.norm.const_mul rightLineBound).mono'
    ((negLogL_continuous_right χ).aestronglyMeasurable.mul hG.aestronglyMeasurable)
  refine Eventually.of_forall fun t => ?_
  simp only [Pi.mul_apply,norm_mul]
  exact mul_le_mul_of_nonneg_right (negLogL_bound_right χ (by simp [verticalPoint])) (norm_nonneg _)

/-- A uniform GRH estimate for the complex exponentially smoothed von Mangoldt twist. -/
theorem primitive_smoothedTwist_bound :
    ∃ C : ℝ, 0<C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      (∀ s : ℂ, 0<s.re → s.re<1 → χ.LFunction s=0 → s.re=1/2) →
      ∀ z : ℂ, 0<z.re → ‖z‖≤1 →
        let T := ‖z‖/z.re
        ‖smoothedTwist χ z - (if χ=1 then z⁻¹ else 0)‖ ≤
          C*(‖z‖^(-(1/2):ℝ)*T)*(Real.log ((q:ℝ)*(2+T))+2) := by
  classical
  let A := 4*leftGammaConst
  let B := 6*(10/Real.log (23/22))*Real.sqrt (2*Real.pi)
  have hA : 0≤A := by
    dsimp [A,leftGammaConst]
    positivity [contourLogDerivBound_pos, Real.Gamma_pos_of_pos (by norm_num : 0 < (1/4:ℝ)),
      Real.Gamma_pos_of_pos (by norm_num : 0 < (1/2:ℝ))]
  have hB : 0≤B := by dsimp [B]; positivity [Real.log_pos (by norm_num : (1:ℝ)<23/22)]
  refine ⟨A+B+2,by positivity,?_⟩
  intro q _ χ hp hGRH z hz hz₁
  let T := ‖z‖/z.re
  let S := (‖z‖^(-(1/2):ℝ)*T)*(Real.log ((q:ℝ)*(2+T))+2)
  let F := twistIntegrand χ z
  let W := ∫ t : ℝ, F (vertical 2 t)
  let m := if χ=1 then z⁻¹ else 0
  have hT : 1 ≤ T := (one_le_div hz).2 (Complex.re_le_norm z)
  have hq : 1 ≤ (q:ℝ) := by exact_mod_cast q.pos_of_neZero
  have hN : 0<‖z‖ := hz.trans_le (Complex.re_le_norm z)
  have hS : 1≤S := by
    have hlog := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq (by linarith : 1≤2+T))
    have hpow : 1≤‖z‖^(-(1/2):ℝ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hN hz₁ (by norm_num)
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hpow hT) (by linarith)
  obtain ⟨u,v,hu,hv,hsafe,hbu,htv⟩ := gamma_good_horizontals χ hp hGRH hz
  let R (n : ℕ) := ‖W-(∫ t : ℝ in u n..v n, F (vertical 2 t))‖
  let H (n : ℕ) := ‖gammaHorizontal χ z (u n)‖+‖gammaHorizontal χ z (v n)‖
  have hR : Tendsto R atTop (𝓝 0) := by
    have he := (intervalIntegral_tendsto_integral (twistIntegrand_integrable_right χ hz) hu hv).const_sub W
    simpa only [R,W,F,sub_self,norm_zero] using he.norm
  have hH : Tendsto H atTop (𝓝 0) := by simpa only [H,add_zero] using hbu.add htv
  have hineq (n : ℕ) : ‖smoothedTwist χ z-m‖ ≤ (B*S+1)+R n+A*S+2*H n+1 := by
    obtain ⟨hun,hvn,havoid⟩ := hsafe n
    obtain ⟨Z,hZ,hrect⟩ := character_weighted_rectangle_of_GRH χ (gammaKernel z)
      (fun _ hs => gammaKernel_analyticAt hz hs) (a:=1/4) (b:=2) (by norm_num) (by norm_num)
      (by norm_num) hun hvn hGRH havoid
    let Zsum := ∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℂ)*gammaKernel z ρ
    have hzsum : ‖Zsum‖≤B*S := by
      have h := primitive_gamma_zero_sum_bound χ hp hGRH hz Z (fun ρ hρ => by
        obtain ⟨h₁,h₂,_,_,h₃⟩ := (hZ ρ).mp hρ
        exact ⟨h₁,h₂,h₃⟩)
      simpa only [S,B,T,Zsum,gammaKernel,mul_assoc] using h
    have hden : (2*(Real.pi:ℂ)*I) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
    have hmass : gammaKernel z 1 = z⁻¹ := by simp [gammaKernel,Complex.cpow_neg_one]
    have hNrect : rectangleBoundary (1/4) 2 (u n) (v n) F / (2*Real.pi*I) = m-Zsum := by
      rw [show rectangleBoundary (1/4) 2 (u n) (v n) F = _ from hrect,mul_div_cancel_left₀ _ hden,hmass]
    have hres : ‖rectangleBoundary (1/4) 2 (u n) (v n) F / (2*Real.pi*I) -
        (if χ=1 then z⁻¹+1/2 else 0)‖ ≤ B*S+1 := by
      rw [hNrect]
      have hgap : ‖m-(if χ=1 then z⁻¹+1/2 else 0)‖ ≤ 1 := by by_cases hχ : χ=1 <;> norm_num [m,hχ]
      calc
        _ = ‖-Zsum+(m-(if χ=1 then z⁻¹+1/2 else 0))‖ := by congr 1; abel
        _ ≤ ‖-Zsum‖+‖m-(if χ=1 then z⁻¹+1/2 else 0)‖ := norm_add_le _ _
        _ ≤ _ := by rw [norm_neg]; exact add_le_add hzsum hgap
    have hleft := gamma_left_edge χ hp hGRH hz hz₁ (hun.le.trans hvn.le)
    have hleft' : ‖∫ t : ℝ in u n..v n, F (vertical (1/4) t)‖≤A*S := by
      simpa only [A,S,mul_assoc] using hleft
    apply sharp_sum_error_of_rectangle F (χ=1) (a:=1/4) (b:=2) (u:=u n) (v:=v n)
      (by simpa only [F,twistIntegrand,vertical,Complex.ofReal_ofNat] using smoothedTwist_eq_right_integral χ hz)
      hres (le_refl _) hleft'
    · exact le_add_of_nonneg_right (norm_nonneg _)
    · exact le_add_of_nonneg_left (norm_nonneg _)
  have hfin := le_of_tendsto_of_tendsto' tendsto_const_nhds
    (((((hR.const_add (B*S+1)).add_const (A*S)).add (hH.const_mul 2)).add_const 1)) hineq
  simp only [mul_zero,add_zero] at hfin
  calc
    _ ≤ (B*S+1)+A*S+1 := hfin
    _ ≤ (A+B+2)*S := by nlinarith only [hS]
    _ = _ := by dsimp only [S,T]; ring

end GoldbachDensity

namespace GoldbachDensity

open Complex Real ArithmeticFunction GoldbachDensityCircle

theorem additive_dirichlet_arc_bound
    (hGRH : ∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ),
      0<s.re → s.re<1 → χ.LFunction s=0 → s.re=1/2) {η : ℝ} (hη : 0<η) :
    ∃ C : ℝ, 0<C ∧ ∀ {X : ℝ} {q : ℕ} [NeZero q] {b : ℝ}, 256≤X →
      (q:ℝ)≤Real.sqrt X → |b| ≤ (2/Real.sqrt X)/q → ∀ g : ZMod q → ℂ, (∀ u, ‖g u‖=1) →
      let z : ℂ := ((X⁻¹:ℝ):ℂ)-2*(Real.pi:ℂ)*(b:ℂ)*I
      ‖(∑' n : ℕ, g (n:ZMod q)*((vonMangoldt n:ℂ)*Complex.exp (-(z*n)))) -
        charCoefficient (fun u : (ZMod q)ˣ => g (u:ZMod q)) 1*z⁻¹‖ ≤ C*X^(3/4+η) := by
  obtain ⟨C,hC,hprimitive⟩ := primitive_smoothedTwist_bound
  let J := Real.log (3+4*Real.pi)+2+1/η
  let A := 20/Real.log 2
  let K := Real.sqrt (1+4*Real.pi)
  have hJ₀ : 0≤Real.log (3+4*Real.pi) := Real.log_nonneg (by linarith [Real.pi_pos])
  have hJ : 0<J := by dsimp [J]; positivity
  have hA : 0<A := by dsimp [A]; positivity [Real.log_pos (by norm_num : (1:ℝ)<2)]
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨2*A+C*K*J,by positivity,?_⟩
  intro X q _ b hX hqs hb g hg
  let z : ℂ := ((X⁻¹:ℝ):ℂ)-2*(Real.pi:ℂ)*(b:ℂ)*I
  let T := ‖z‖/z.re
  let U := ‖z‖^(-(1/2):ℝ)*T
  let L := Real.log ((q:ℝ)*(2+T))+2
  let P := X^(1/4:ℝ)
  let V := X^η
  have hX₁ : 1≤X := by linarith
  have hx : 0<X := by linarith
  have hq : 1≤(q:ℝ) := by exact_mod_cast NeZero.one_le (n:=q)
  have hqp : 0<(q:ℝ) := by linarith
  have hP : 1≤P := Real.one_le_rpow hX₁ (by norm_num)
  have hV : 1≤V := Real.one_le_rpow hX₁ hη.le
  have hroot : 16≤Real.sqrt X := (Real.le_sqrt (by norm_num) hx.le).2 (by norm_num; linarith)
  have hrootX : Real.sqrt X ≤ X := by
    rw [Real.sqrt_eq_rpow]
    simpa using Real.rpow_le_rpow_of_exponent_le hX₁ (by norm_num : (1/2:ℝ)≤1)
  have hz : z.re=X⁻¹ := by simp [z,Complex.mul_re,Complex.mul_im]
  have hzpos : 0<z.re := hz ▸ inv_pos.mpr hx
  have hzbd : ‖z‖≤1 := by
    have hab : |b| ≤ 1/8 := calc
      _ ≤ (2/Real.sqrt X)/q := hb
      _ ≤ 2/Real.sqrt X := div_le_self (by positivity) hq
      _ ≤ _ := (div_le_iff₀ (by linarith : 0<Real.sqrt X)).mpr (by linarith)
    have hi : X⁻¹≤1/256 := by
      rw [← one_div]; exact one_div_le_one_div_of_le (by norm_num) hX
    have hn : ‖z‖ ≤ X⁻¹+2*Real.pi*|b| := by
      apply (norm_sub_le _ _).trans_eq
      simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx,abs_of_pos Real.pi_pos]
    nlinarith only [hn,hi,mul_le_mul_of_nonneg_left hab (show 0≤2*Real.pi by positivity),Real.pi_lt_d2]
  have hT : 1≤T := (one_le_div hzpos).2 (Complex.re_le_norm z)
  have hU : 0≤U := mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (by linarith)
  have hL : 0≤L := by
    have h := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq (by linarith : 1≤2+T))
    dsimp [L]; linarith
  have hmain := mellin_scale_on_dirichlet_arc hX₁ (NeZero.pos q) hqs hb
  change Real.sqrt q * U ≤ K*X^(3/4:ℝ) ∧ (q:ℝ)*(2+T)≤(3+4*Real.pi)*Real.sqrt X at hmain
  have hlog : L ≤ J*V := by
    have h0 : 0<(q:ℝ)*(2+T) := mul_pos hqp (by linarith)
    have hfac : 0<3+4*Real.pi := by positivity
    have hh := Real.log_le_log h0 (hmain.2.trans (mul_le_mul_of_nonneg_left hrootX hfac.le))
    rw [Real.log_mul hfac.ne' hx.ne'] at hh
    have hpow := Real.log_le_rpow_div hx.le hη
    have hex := mul_le_mul_of_nonneg_left hV (show 0≤Real.log (3+4*Real.pi)+2 by linarith)
    dsimp only [J,L]
    change Real.log X ≤ V/η at hpow
    rw [div_eq_mul_inv] at hpow
    rw [one_div]
    nlinarith only [hh,hpow,hex]
  have hφ : Real.sqrt q.totient ≤ Real.sqrt q := Real.sqrt_le_sqrt (by exact_mod_cast Nat.totient_le q)
  have hsP : Real.sqrt q ≤ P := by
    apply (Real.sqrt_le_sqrt hqs).trans_eq
    dsimp [P]; simp_rw [Real.sqrt_eq_rpow]; rw [← Real.rpow_mul hx.le]; norm_num
  have hmass : badMass q X ≤ A*P^2 := by
    have hlogq := Real.log_le_log hqp (hqs.trans hrootX)
    have H := Real.log_le_rpow_div hx.le (by norm_num : (0:ℝ)<1/4)
    have hlogX : Real.log X≤4*P := by simpa only [P,div_div_eq_mul_div,div_one,mul_comm] using H
    have hl₂ : 0<Real.log 2 := Real.log_pos (by norm_num)
    have hlex : Real.log X+1 ≤ 5*P := by linarith
    apply (badMass_bound q hX₁).trans
    apply (mul_le_mul (div_le_div_of_nonneg_right (hlogq.trans hlogX) hl₂.le) hlex
      (by linarith [Real.log_nonneg hX₁]) (by positivity)).trans_eq
    dsimp [A]; ring
  let w := fun n : ℕ => (vonMangoldt n:ℂ)*Complex.exp (-(z*n))
  have hw (n : ℕ) : ‖w n‖ = ‖mangoldtWeight X n‖ := by
    simp only [w,norm_mul,Complex.norm_exp,damped_norm,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg vonMangoldt_nonneg,Complex.neg_re]
    rw [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,mul_zero,sub_zero,hz]
    congr 2; ring
  have hprim (d : ℕ) [NeZero d] (hd : d ∣ q) (χ : DirichletCharacter ℂ d) (hp : χ.IsPrimitive) :
      ‖sequenceTwist χ w-(if χ=1 then z⁻¹ else 0)‖ ≤ C*U*L := by
    have heq : sequenceTwist χ w = smoothedTwist χ z := by
      simp only [sequenceTwist,smoothedTwist,w,mul_assoc]
    rw [heq]
    have hdl : 0<(d:ℝ) := Nat.cast_pos.mpr (NeZero.pos d)
    have hdq : (d:ℝ)≤q := by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) hd
    apply (hprimitive d χ hp (hGRH d χ) z hzpos hzbd).trans
    exact mul_le_mul_of_nonneg_left (add_le_add (Real.log_le_log (mul_pos hdl (by linarith : 0<2+T))
      (mul_le_mul_of_nonneg_right hdq (by linarith))) (le_refl 2)) (mul_nonneg hC.le hU)
  have hsum := additive_from_primitive q g hg hX₁ w hw z⁻¹ (C*U*L) (by positivity) hprim
  have hbad₀ : 0≤badMass q X := tsum_nonneg fun n => by split_ifs <;> positivity [vonMangoldt_nonneg (n:=n)]
  have hP3 : P^3 = X^(3/4:ℝ) := by
    dsimp [P]; rw [← Real.rpow_mul_natCast hx.le]; norm_num
  have hsmall : (1+Real.sqrt q.totient)*badMass q X ≤ 2*A*X^(3/4:ℝ) := by
    have hbound : 1+Real.sqrt q.totient ≤ 2*P := by linarith [hφ.trans hsP]
    apply (mul_le_mul hbound hmass hbad₀ (by linarith)).trans_eq
    rw [← hP3]; ring
  have hbig : Real.sqrt q.totient*(C*U*L) ≤ C*K*J*(X^(3/4:ℝ)*V) := by
    have hbase := (mul_le_mul_of_nonneg_right hφ hU).trans hmain.1
    calc
      _ = C*((Real.sqrt q.totient*U)*L) := by ring
      _ ≤ C*((K*X^(3/4:ℝ))*(J*V)) := mul_le_mul_of_nonneg_left
        (mul_le_mul hbase hlog hL (by positivity)) hC.le
      _ = _ := by ring
  apply hsum.trans
  calc
    _ = (1+Real.sqrt q.totient)*badMass q X+Real.sqrt q.totient*(C*U*L) := by ring
    _ ≤ 2*A*X^(3/4:ℝ)+C*K*J*(X^(3/4:ℝ)*V) := add_le_add hsmall hbig
    _ ≤ (2*A+C*K*J)*(X^(3/4:ℝ)*V) := by
      nlinarith only [mul_le_mul_of_nonneg_left hV (show 0≤2*A*X^(3/4:ℝ) by positivity)]
    _ = _ := by rw [Real.rpow_add hx]

end GoldbachDensity

namespace GoldbachDensity

open Complex GoldbachDensityCircle AddCircle ArithmeticFunction Finset
open scoped ComplexConjugate

noncomputable def rationalAdditivePhase (q a : ℕ) [NeZero q] (u : ZMod q) : ℂ :=
  ZMod.stdAddChar ((a:ZMod q)*u)

theorem norm_rationalAdditivePhase (q a : ℕ) [NeZero q] (u : ZMod q) :
    ‖rationalAdditivePhase q a u‖ = 1 := by simp [rationalAdditivePhase,ZMod.stdAddChar_apply]

theorem rationalAdditivePhase_nat (q a n : ℕ) [NeZero q] :
    rationalAdditivePhase q a (n:ZMod q) = Complex.exp (2*Real.pi*I*a*n/q) := by
  dsimp only [rationalAdditivePhase]
  have h : (a:ZMod q)*(n:ZMod q) = (((a*n:ℕ):ℤ):ZMod q) := by push_cast; rfl
  rw [h,ZMod.stdAddChar_coe]
  push_cast; congr 1; ring

private theorem conjugate_rationalPhase (q a n : ℕ) :
    (starRingEnd ℂ) (rationalPhase a q n) = Complex.exp (2*Real.pi*I*a*n/q) := by
  rw [rationalPhase,← Complex.exp_conj]
  simp only [map_div₀,map_mul,map_neg,map_ofNat,map_natCast,Complex.conj_I,Complex.conj_ofReal]
  congr 1; ring

/-- The principal character's coefficient equals the rational arc amplitude. -/
theorem rationalAdditive_principal (q a : ℕ) [NeZero q] (hcop : a.Coprime q) :
    charCoefficient (fun u : (ZMod q)ˣ => rationalAdditivePhase q a u) 1 =
      ((moebius q:ℤ):ℂ)/(q.totient:ℂ) := by
  classical
  unfold charCoefficient
  congr 1
  have hR := congrArg (starRingEnd ℂ) (coprime_ramanujan_eq_moebius (NeZero.pos q) hcop)
  simp only [map_sum,map_intCast] at hR
  apply Eq.trans _ hR
  apply Finset.sum_bij (fun (u : (ZMod q)ˣ) _ => (u:ZMod q).val)
  · intro u _
    exact mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt _), (ZMod.isUnit_iff_coprime _ _).mp
      (by simp)⟩
  · intro u _ v _ h
    apply Units.ext
    simpa using congrArg (fun n : ℕ => (n:ZMod q)) h
  · intro n hn
    obtain ⟨hn,hc⟩ := mem_filter.mp hn
    exact ⟨ZMod.unitOfCoprime n hc,mem_univ _,by simp [ZMod.val_natCast_of_lt (mem_range.mp hn)]⟩
  · intro u _
    have h := rationalAdditivePhase_nat q a (u:ZMod q).val
    simp only [ZMod.natCast_zmod_val] at h
    dsimp only
    rw [h]
    rw [conjugate_rationalPhase]; simp

noncomputable def arcDampedWeight (z : ℂ) (n : ℕ) : ℂ := (vonMangoldt n:ℂ)*Complex.exp (-(z*n))

theorem norm_arcDampedWeight (X b : ℝ) (n : ℕ) :
    ‖arcDampedWeight (((X⁻¹:ℝ):ℂ)-2*(Real.pi:ℂ)*(b:ℂ)*I) n‖ = ‖mangoldtWeight X n‖ := by
  have hr : (-((((X⁻¹:ℝ):ℂ)-2*(Real.pi:ℂ)*(b:ℂ)*I)*(n:ℂ))).re = -(n:ℝ)/X := by
    have hz : (((X⁻¹:ℝ):ℂ)-2*(Real.pi:ℂ)*(b:ℂ)*I).re=X⁻¹ := by simp [Complex.mul_re,Complex.mul_im]
    simp only [Complex.neg_re,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,hz,mul_zero,sub_zero]
    rw [div_eq_mul_inv]; ring
  rw [damped_norm,arcDampedWeight,norm_mul,Complex.norm_exp,hr,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg vonMangoldt_nonneg]

theorem local_mangoldt_sum (X b : ℝ) (q a : ℕ) [NeZero q] :
    positiveFrequencySeries (mangoldtWeight X) ((b+arcCenter (q,a):ℝ):AddCircle (1:ℝ)) =
      ∑' n : ℕ, rationalAdditivePhase q a n * arcDampedWeight
        (((X⁻¹:ℝ):ℂ)-2*(Real.pi:ℂ)*(b:ℂ)*I) n := by
  unfold positiveFrequencySeries
  apply tsum_congr
  intro n
  rw [rationalAdditivePhase_nat,arcDampedWeight,mangoldtWeight,arcCenter,fourier_coe_apply]
  push_cast
  rw [mul_assoc (vonMangoldt n:ℂ), mul_left_comm (Complex.exp _) (vonMangoldt n:ℂ),
    ← Complex.exp_add,← Complex.exp_add]
  congr 2
  simp [div_eq_mul_inv]; ring

end GoldbachDensity

namespace GoldbachDensity

open GoldbachDensityCircle Complex

/-- At every Dirichlet approximation the actual Mangoldt generating function
is within `O(X^(3/4+η))` of the rational major-arc profile. -/
theorem rational_arc_error (hGRH : ∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ),
    0 < s.re → s.re < 1 → χ.LFunction s=0 → s.re=1/2) {η : ℝ} (he : 0<η) :
    ∃ C : ℝ, 0<C ∧ ∀ (X : ℝ) (i : ℕ × ℕ) (b : ℝ), 256 ≤ X → 0 < i.1 → i.2.Coprime i.1 →
      (i.1:ℝ) ≤ Real.sqrt X → |b| ≤ (2/Real.sqrt X)/i.1 →
      ‖positiveFrequencySeries (mangoldtWeight X) ((b+arcCenter i:ℝ):AddCircle (1:ℝ)) -
        majorProfile X i.1 b‖ ≤ C * X^(3/4+η) := by
  obtain ⟨C,hC,H⟩ := additive_dirichlet_arc_bound hGRH he
  refine ⟨C,hC,?_⟩
  rintro X ⟨q,a⟩ b hX hq hcop hqs hb
  have : NeZero q := ⟨hq.ne'⟩
  have h := H hX hqs hb (rationalAdditivePhase q a) (norm_rationalAdditivePhase q a)
  dsimp only at h ⊢
  rw [rationalAdditive_principal q a hcop] at h
  rw [local_mangoldt_sum,majorProfile,div_eq_mul_inv _ (((X⁻¹:ℝ):ℂ)-2*(Real.pi:ℂ)*(b:ℂ)*I)]
  exact h

end GoldbachDensity

namespace GoldbachDensity

open Finset AddCircle MeasureTheory GoldbachDensityCircle

private instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

private theorem sum_inverse_totient_bound {η : ℝ} (hη : 0<η) :
    ∃ D : ℝ, 0<D ∧ ∀ {Q : ℕ} {X : ℝ}, 1≤X → (Q:ℝ)≤X →
      (∑ q∈Icc 1 Q, (q.totient:ℝ)⁻¹) ≤ D*X^η := by
  let e := η/2
  have he : 0<e := half_pos hη
  obtain ⟨C,hC,H⟩ := totient_ratio_bound he
  let w := fun q : ℕ => (q:ℝ)^(-1-e)
  have hw : Summable w := Real.summable_nat_rpow.mpr (by linarith only [he])
  have hw0 (q : ℕ) : 0 ≤ w q := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsum : 0 ≤ ∑' q, w q := tsum_nonneg hw0
  refine ⟨C*((∑' q, w q)+1),by positivity,?_⟩
  intro Q X hx hQ
  have hx0 := zero_lt_one.trans_le hx
  have hb (q : ℕ) (hq : q∈Icc 1 Q) : (q.totient:ℝ)⁻¹ ≤ (C*X^η)*w q := by
    have hq0 : 0<q := (mem_Icc.mp hq).1
    have hqr : 0<(q:ℝ) := Nat.cast_pos.mpr hq0
    have hqx : (q:ℝ)≤X := (Nat.cast_le.mpr (mem_Icc.mp hq).2).trans hQ
    have hφ := H q hq0
    have hd : (q.totient:ℝ)⁻¹ ≤ C*(q:ℝ)^e/q := by
      apply (le_div_iff₀ hqr).mpr
      simpa only [div_eq_mul_inv,mul_comm (q:ℝ)] using hφ
    have hi : C*(q:ℝ)^e/q = C*(q:ℝ)^η*w q := by
      dsimp [w]
      rw [mul_assoc,← Real.rpow_add hqr,mul_div_assoc,← Real.rpow_sub_one hqr.ne']
      congr 2
      dsimp [e]; ring
    rw [hi] at hd
    exact hd.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hqr.le hqx hη.le) hC.le) (hw0 _))
  calc
    _ ≤ ∑ q∈Icc 1 Q, (C*X^η)*w q := sum_le_sum hb
    _ = (C*X^η)*(∑ q∈Icc 1 Q, w q) := (mul_sum ..).symm
    _ ≤ (C*X^η)*((∑' q, w q)+1) := mul_le_mul_of_nonneg_left
      ((hw.sum_le_tsum _ (fun i _ => hw0 i)).trans (by linarith)) (by positivity)
    _ = _ := by ring

/-- Total energy of the disjoint rational-arc model. Each denominator
contributes once for each of its totient-many reduced numerators. -/
theorem major_model_energy {η : ℝ} (hη : 0<η) : ∃ C : ℝ, 0<C ∧
    ∀ {X P : ℝ} {Q : ℕ}, 1≤X → 0≤P → (Q:ℝ)≤X → 2*P*Q<X →
    (∫ x, ‖arcModel X P Q (majorProfile X) x‖^2 ∂haarAddCircle) ≤ C*X^(1+η) := by
  obtain ⟨D,hD,H⟩ := sum_inverse_totient_bound hη
  refine ⟨Real.pi*D,by positivity,?_⟩
  intro X P Q hx hp hQ hsep
  have hx0 := zero_lt_one.trans_le hx
  rw [arcModel_energy X P Q _ (majorProfile_continuous hx0) hx0 hp hsep,sum_arcIndices]
  apply le_trans (b := ∑ q ∈ Icc 1 Q, (Real.pi*X)*(q.totient:ℝ)⁻¹)
  · apply sum_le_sum
    intro q hq
    have hq0 : 0<q := (mem_Icc.mp hq).1
    have hφ : 0<(q.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq0)
    have hcard : ((range q).filter (fun a => a.Coprime q)).card=q.totient := by
      simpa only [Nat.coprime_comm] using (Nat.totient_eq_card_coprime q).symm
    simp only [sum_const,nsmul_eq_mul,hcard]
    have h := majorProfile_interval_energy hx0 hq0 (h:=arcWidth X P q)
      (div_nonneg hp (mul_nonneg (Nat.cast_nonneg _) hx0.le))
    apply (mul_le_mul_of_nonneg_left h hφ.le).trans_eq
    field_simp
  · rw [← mul_sum,Real.rpow_add hx0,Real.rpow_one]
    calc
      _ ≤ (Real.pi*X)*(D*X^η) := mul_le_mul_of_nonneg_left (H hx hQ) (by positivity)
      _ = _ := by ring

private theorem mangoldt_energy_power {η : ℝ} (hη : 0<η) :
    ∃ C : ℝ, 0<C ∧ ∀ {X : ℝ}, 1≤X →
      (∫ t, ‖positiveFrequencySeries (mangoldtWeight X) t‖^2 ∂haarAddCircle) ≤ C*X^(1+η) := by
  let e := η/2
  have he : 0<e := half_pos hη
  let D := e⁻¹+2
  have hd : 0<D := by dsimp [D]; positivity
  refine ⟨2*D^2,by positivity,?_⟩
  intro X hx
  have hx0 := zero_lt_one.trans_le hx
  have h1 := Real.one_le_rpow hx he.le
  have hl := Real.log_le_rpow_div hx0.le he
  have hlog : Real.log X+2 ≤ D*X^e := by
    dsimp [D]; rw [div_eq_mul_inv] at hl; nlinarith only [hl,h1]
  have hs := pow_le_pow_left₀ (by linarith [Real.log_nonneg hx]) hlog 2
  have hp : (X^e)^2 = X^η := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hx0.le]
    congr 1; dsimp [e]; ring
  rw [mul_pow,hp] at hs
  apply (mangoldt_series_energy hx).trans
  rw [Real.rpow_add hx0,Real.rpow_one]
  calc
    _ ≤ (D^2*X^η)*(2*X) := mul_le_mul hs (by linarith) (by linarith) (by positivity)
    _ = _ := by ring

/-- Total energy of the sum of the smoothed Mangoldt series and the
piecewise major-arc approximation, uniformly in the cutoffs. -/
theorem combined_arc_energy {η : ℝ} (hη : 0<η) : ∃ C : ℝ, 0<C ∧
    ∀ (X : ℝ) (Q : ℕ), 1≤X → 0<Q → (Q:ℝ)≤X → 2*(Q:ℝ)*Q<X →
    (∫ t, ‖positiveFrequencySeries (mangoldtWeight X) t+
      arcModel X Q Q (majorProfile X) t‖^2 ∂haarAddCircle) ≤ C*X^(1+η) := by
  obtain ⟨A,hA,HA⟩ := mangoldt_energy_power hη
  obtain ⟨B,hB,HB⟩ := major_model_energy hη
  refine ⟨2*(A+B),by positivity,?_⟩
  intro X Q hx hq0 hQ hsep
  let F := positiveFrequencySeries (mangoldtWeight X)
  let V := arcModel X Q Q (majorProfile X)
  have hF : MemLp F 2 haarAddCircle := (series_continuous (mangoldtWeight_summable hx)).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hV : MemLp V 2 haarAddCircle := arcModel_memLp X Q Q _ (majorProfile_continuous (zero_lt_one.trans_le hx)) _
  have hF' : Integrable (fun t => ‖F t‖^2) haarAddCircle := hF.norm.integrable_sq
  have hV' : Integrable (fun t => ‖V t‖^2) haarAddCircle := hV.norm.integrable_sq
  have hsum : MemLp (fun t => F t+V t) 2 haarAddCircle := hF.add hV
  have hI : (∫ t, ‖F t+V t‖^2 ∂haarAddCircle) ≤ ∫ t, 2*(‖F t‖^2+‖V t‖^2) ∂haarAddCircle := by
    apply integral_mono hsum.norm.integrable_sq ((hF'.add hV').const_mul 2)
    intro t
    change ‖F t+V t‖^2 ≤ 2*(‖F t‖^2+‖V t‖^2)
    have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (F t) (V t)) 2
    nlinarith only [h,sq_nonneg (‖F t‖-‖V t‖)]
  rw [integral_const_mul,integral_add hF' hV'] at hI
  apply hI.trans
  calc
    _ ≤ 2*(A*X^(1+η)+B*X^(1+η)) := mul_le_mul_of_nonneg_left
      (add_le_add (HA hx) (HB hx (Nat.cast_nonneg Q) hQ hsep)) (by norm_num)
    _ = _ := by ring

end GoldbachDensity

namespace GoldbachDensity

open Finset AddCircle GoldbachDensityCircle GoldbachDensityTransfer MeasureTheory
open scoped Topology

private instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

set_option maxHeartbeats 1500000 in
/-- A uniform approximation on the Dirichlet arcs and an integrated energy
bound give the stated exceptional-set exponent by Bessel's inequality. -/
theorem count_from_arc_estimates {ε : ℝ} (he : 0<ε)
    (hloc : ∃ C : ℝ, 0<C ∧ ∀ (X : ℝ) (i : ℕ × ℕ) (b : ℝ),
      256≤X → 0 < i.1 → i.2.Coprime i.1 → (i.1:ℝ)≤Real.sqrt X →
      |b|≤(2/Real.sqrt X)/i.1 →
      ‖positiveFrequencySeries (mangoldtWeight X) ((b+arcCenter i : ℝ):AddCircle (1:ℝ))-
        majorProfile X i.1 b‖ ≤ C*X^(3/4+ε/3))
    (henergy : ∃ C : ℝ, 0<C ∧ ∀ (X : ℝ) (Q : ℕ),
      1≤X → 0<Q → (Q:ℝ)≤X → 2*(Q:ℝ)*Q<X →
      (∫ t, ‖positiveFrequencySeries (mangoldtWeight X) t +
        arcModel X (Q:ℝ) Q (majorProfile X) t‖^2 ∂haarAddCircle) ≤ C*X^(1+ε/3)) :
    ∃ C : ℝ, 0<C ∧ ∀ X : ℕ, 1≤X → ((exceptionSet X).card:ℝ) ≤ C*(X:ℝ)^(1/2+ε) := by
  classical
  obtain ⟨L,hL,Hloc⟩ := hloc
  obtain ⟨B,hB,Hminor⟩ := minor_profile_bound (show 0<ε/3 by positivity)
  obtain ⟨D,hD,Henergy⟩ := henergy
  obtain ⟨c,hc,P₀,Hlower⟩ := majorArcCoefficient_lower
  obtain ⟨X₀,_,Hcut⟩ := exists_arc_cutoffs P₀
  let N := ⌈max 256 X₀⌉₊
  have hx {X : ℕ} (h : N≤X) : max 256 X₀ ≤ (X:ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr h)
  let F (X : ℕ) := positiveFrequencySeries (mangoldtWeight X)
  let V (X Q : ℕ) := arcModel X (Q:ℝ) Q (majorProfile X)
  let m (X Q n : ℕ) := fourierCoeff (fun t => (V X Q t)^2) (n:ℤ)
  let A := (L+B)^2*D
  have H (X : ℕ) (hN : N≤X) : ∃ Q : ℕ,
      (∀ n : ℕ, X/2<n → n≤X → n % 2 = 0 → c*X≤‖m X Q n‖) ∧
      ∑ n ∈ range (X+1), ‖((Real.exp (-(n:ℝ)/X)*mangoldtConvolution n:ℝ):ℂ)-m X Q n‖^2
        ≤ A*(X:ℝ)^(2+(1/2+ε)) := by
    have h256 : (256:ℝ)≤X := (le_max_left ..).trans (hx hN)
    have h1 : (1:ℝ)≤X := by linarith
    have hp : 0<(X:ℝ) := by linarith
    obtain ⟨M,Q,hPQ,hQ,hQM,hMs,hs,hdir,hwidth,hpow,hsize⟩ :=
      Hcut X ((le_max_right ..).trans (hx hN))
    have hQx : (Q:ℝ)≤X := ((Nat.cast_le.mpr hQM).trans hMs).trans (Real.sqrt_le_self_iff.mpr (Or.inr h1))
    refine ⟨Q,?_,?_⟩
    · intro n hh hn heven
      have hh' : X≤2*n := by omega
      have hreal : (X:ℝ)≤2*n := by exact_mod_cast hh'
      change _ ≤ ‖fourierCoeff (fun t => (arcModel X (Q:ℝ) Q (majorProfile X) t)^2) (n:ℤ)‖
      rw [arcModel_coeff_eq_majorArcCoefficient Q n hp hs (majorProfile_continuous hp)]
      exact Hlower _ _ _ hPQ hp (by linarith) (Nat.cast_le.mpr hn)
        (hn.trans (by exact_mod_cast hpow)) (Nat.even_iff.mpr heven)
    · let S := (X:ℝ)^(3/4+ε/3)
      have hsup := global_error_of_rational_approximations (F X) (majorProfile X)
        hp (Nat.cast_nonneg Q) hs (hQ.trans_le hQM) hQM hdir hwidth
        (show 0 ≤ B*S from mul_nonneg hB.le (Real.rpow_nonneg hp.le _))
        (A:=L*S)
        (fun i hi b hb => by
          obtain ⟨hq,hqM,_,ha⟩ := mem_majorArcIndices.mp hi
          exact Hloc X i b h256 hq ha ((Nat.cast_le.mpr hqM).trans hMs) hb)
        (fun i hi b _ hminor => by
          obtain ⟨hq,hqM,_,_⟩ := mem_majorArcIndices.mp hi
          exact Hminor hp hq hQ (((Nat.cast_le.mpr hqM).trans hMs).trans (Real.sqrt_le_self_iff.mpr (Or.inr h1))) hsize hminor)
      have hF : MemLp (F X) 2 haarAddCircle := (series_continuous
        (mangoldtWeight_summable h1)).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hV := arcModel_memLp X (Q:ℝ) Q _ (majorProfile_continuous hp) 2
      have hcoeff := finite_coefficient_error (range (X+1)) (F X) (V X Q) hF hV
        (Filter.Eventually.of_forall hsup)
      have hco (n : ℕ) : fourierCoeff (fun t => (F X t)^2) (n:ℤ) =
          ((Real.exp (-(n:ℝ)/X)*mangoldtConvolution n:ℝ):ℂ) := mangoldt_series_coefficient h1 n
      simp only [hco] at hcoeff
      apply hcoeff.trans
      calc
        _ ≤ (L*S+B*S)^2 * (D*(X:ℝ)^(1+ε/3)) := mul_le_mul_of_nonneg_left
          (Henergy X Q h1 hQ hQx hs) (sq_nonneg _)
        _ = A*((X:ℝ)^(3/4+ε/3)*(X:ℝ)^(3/4+ε/3)*(X:ℝ)^(1+ε/3)) := by dsimp [A,S]; ring
        _ = _ := by rw [← Real.rpow_add hp,← Real.rpow_add hp]; congr 2; ring
  let Q (X : ℕ) := if h : N≤X then (H X h).choose else 0
  have HQ (X : ℕ) (h : N≤X) : Q X = (H X h).choose := by simp [Q,h]
  exact exceptionalCount_of_smoothed_mean_square (by positivity) hc (fun X n => m X (Q X) n) N
    (fun X h => by rw [HQ X h]; exact (H X h).choose_spec.1)
    (fun X h => by rw [HQ X h]; exact (H X h).choose_spec.2)

end GoldbachDensity

/-- Under the generalized Riemann hypothesis for all Dirichlet characters,
the number of even integers up to X without a Goldbach representation
is bounded by a constant times X to the power one half plus ε. -/
theorem PEqualNP.Outside.L_goldbach_grh_goldbach_exception_density :
    (∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ),
      0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2) →
    let E : ℕ → ℕ := fun X => ((Finset.range (X + 1)).filter (fun n =>
      4 ≤ n ∧ n % 2 = 0 ∧ ((Finset.range (n + 1)).filter (fun p =>
        Nat.Prime p ∧ Nat.Prime (n - p))).card = 0)).card
    ∀ ε : ℝ, 0 < ε → ∃ (C : ℝ) (X₀ : ℕ), 0 < C ∧ ∀ X : ℕ, X₀ ≤ X →
      (E X : ℝ) ≤ C * (X : ℝ) ^ ((1 / 2 : ℝ) + ε) := by
  intro hGRH E ε he
  have hη : 0 < ε/3 := by positivity
  obtain ⟨C,hC,H⟩ := GoldbachDensity.count_from_arc_estimates he
    (GoldbachDensity.rational_arc_error hGRH hη) (GoldbachDensity.combined_arc_energy hη)
  exact ⟨C,1,hC,H⟩
