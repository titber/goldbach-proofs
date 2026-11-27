import Main

theorem CheckerSuite.GRHConsumer :
    RiemannHypothesis ∧ RiemannZetaZerosOnLine ∧ DirichletLNonvanishingRightOfHalf ∧
    DirichletLZerosOnLine ∧ PrimitiveDirichletLZerosOnLine :=
  ⟨riemannHypothesis, riemannZeta_eq_zero_re, LFunction_ne_zero_of_half_lt_re,
    LFunction_eq_zero_re, LFunction_eq_zero_re_of_isPrimitive⟩
