/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.StrictQuotient.QuotientExpressionStrictKFlatTowers

/-! K-flat finite models for strict quotient expressions.

Source: Stacks Project, sites-cohomology.tex, Tags 0G7E, 07A2 and 07A4
(blueprint: lem-pur-quotient-expression-kflat-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures.StrictQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The strict tower construction supplies the input models and K-flatness for every
finite generated expression.  The `Generated` predicate is obtained by forgetting the
constructor history of `Expression`.

Source: Stacks Project, sites-cohomology.tex, Tags 0G7E, 07A2 and 07A4;
(blueprint: lem-pur-quotient-expression-kflat-normalization).
-/
theorem quotientExpressionKFlatModels
    {Z X Y : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (hlZ : ∀ x : Z, IsUnit (l : Z.residueField x))
    (hlX : ∀ x : X, IsUnit (l : X.residueField x))
    (hlY : ∀ x : Y, IsUnit (l : Y.residueField x))
    (r : ℕ) (P : Fin r → CochainComplex (scalarReductionSource l E Y) ℤ)
    (hP : ∀ i : Fin r, CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) (P i))
    (hflat : ∀ (i : Fin r) (k : ℤ), SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) ((P i).X k)) :
    ∃ (N : Fin r → Complex l E Y)
      (κ : ∀ (i : Fin r) (n : ℕ), level l E (N i) n ≅
        ((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj (P i)),
      (∀ (i : Fin r) {m n : ℕ} (hmn : n ≤ m),
        transition l E (N i) hmn ≫
            ((normalizedDVRModuleRes l E Y hmn).mapHomologicalComplex (.up ℤ)).map
              (κ i n).hom =
          (κ i m).hom ≫
            (NatTrans.mapHomologicalComplex (coefficientOrdinaryQuotient l E Y hmn)
              (.up ℤ)).app (P i)) ∧
      (∀ (i : Fin r) (n : ℕ),
        ∃ e : (coefficientFiniteDerivedExtension l E Y n).obj
            (DerivedCategory.Q.obj (P i)) ≅ DerivedCategory.Q.obj (level l E (N i) n),
          e.hom = (coefficientFiniteReductionModel l E Y (P i) (hP i) n).hom ≫
            DerivedCategory.Q.map (κ i n).inv) ∧
      ∀ (W : Scheme.{t}) (K : Complex l E W), Generated l E h f N W K →
        ∀ n : ℕ, Good l E K n := by
  obtain ⟨hc, hu, N, κ, hκ, he, hExpr, htensor, hpull⟩ :=
    quotientExpressionStrictKFlatTowers l E h f hlZ hlX hlY r P hP hflat
  have hsyntax : ∀ (W : Scheme.{t}) (K : Complex l E W),
      Generated l E h f N W K → ∃ A : Expression h f r W, A.interpret l E N = K := by
    intro W K hK
    induction hK with
    | input i => exact ⟨.input i, rfl⟩
    | unitY => exact ⟨.unitY, rfl⟩
    | unitX => exact ⟨.unitX, rfl⟩
    | unitZ => exact ⟨.unitZ, rfl⟩
    | tensor hP hQ ihP ihQ =>
        obtain ⟨A, rfl⟩ := ihP
        obtain ⟨B, rfl⟩ := ihQ
        exact ⟨.tensor A B, rfl⟩
    | pullF hP ihP =>
        obtain ⟨A, rfl⟩ := ihP
        exact ⟨.pullF A, rfl⟩
    | pullH hP ihP =>
        obtain ⟨A, rfl⟩ := ihP
        exact ⟨.pullH A, rfl⟩
    | pullHF hP ihP =>
        obtain ⟨A, rfl⟩ := ihP
        exact ⟨.pullHF A, rfl⟩
  refine ⟨N, κ, hκ, he, ?_⟩
  intro W K hK
  obtain ⟨A, rfl⟩ := hsyntax W K hK
  exact (hExpr W A).2.1

end WeilConjectures.StrictQuotient
