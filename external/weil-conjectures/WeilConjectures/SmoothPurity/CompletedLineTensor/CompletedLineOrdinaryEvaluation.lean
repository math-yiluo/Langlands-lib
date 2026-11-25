/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLineTensorOrdinaryData
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.Algebra.Homology.PoincareDuality.TensorTrilinearUniversal
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement

/-! # Ordinary signed-line scalar evaluation

Source: blueprint sk-def-sp-tate-twist-locally-free, Proof (3), evaluation compatibility.
(blueprint: lem-pur-completed-line-ordinary-evaluation)

The normalized ordinary comparisons preserve evaluation before completion. This is
the ordinary square used to prove the completed evaluation square by conjugation.
-/

@[expose] public noncomputable section
set_option Elab.async false
attribute [local instance 5000] CategoryTheory.HasSheafify.isRightAdjoint
attribute [local instance 5000] Algebra.toModule
attribute [local irreducible] Padic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe t u
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open scoped ChangeOfRings
namespace WeilConjectures
namespace CompletedLineTensor

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted completedCoefficientMap
  completedOrdinaryScalarExtension completedDerivedScalarExtension
  completedScalarCounit completedScalarTensorSection integralScalarExtensionOfUniverses
  completedScalarChangeData completedOrdinaryScalarComplex

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] F)

section SheafSquare

/-- Ordinary completed scalar extension is left adjoint to restriction, with unit `1 ⊗ x`.
Source: Stacks 03D7 (blueprint: lem-pur-completed-line-ordinary-evaluation). -/
private theorem scalarAdjunction :
    ∃ a : completedOrdinaryScalarExtension l E F ι X ⊣
        SheafOfModules.restrictScalars
          ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology X)
            (forget₂ CommRingCat RingCat)).map (completedCoefficientMap l E F ι X)),
      ∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
        (a.unit.app M).val.app U x = completedScalarTensorSection l E F ι X M U 1 x := by
  obtain ⟨a, ha⟩ :=
    (SheafOfModules.sheafRingCoefficientOrdinaryAdjunction
      (completedCoefficientMap l E F ι X)).choose_spec.choose_spec
        (completedOrdinaryScalarExtension l E F ι X)
        (completedOrdinaryScalarExtension_obj l E F ι X)
        (fun f ↦ completedOrdinaryScalarExtension_map l E F ι X f)
  refine ⟨a, ?_⟩
  intro M U x
  let e := eqToIso (completedOrdinaryScalarExtension_obj l E F ι X M)
  have h := ha M ((completedOrdinaryScalarExtension l E F ι X).obj M) e.inv U x
  have he : eqToHom (completedOrdinaryScalarExtension_obj l E F ι X M) ≫ e.inv = 𝟙 _ :=
    e.hom_inv_id
  rw [he, Adjunction.homEquiv_id] at h
  dsimp only [completedScalarTensorSection, e, eqToIso.inv,
    completedOrdinaryScalarExtension] at h ⊢
  with_unfolding_all exact h

set_option backward.isDefEq.respectTransparency false in
/-- Coefficient scalars pass through the scalar-extension generator `1 ⊗ x`.
Source: Stacks 03EK, balancing (blueprint: lem-pur-completed-line-ordinary-evaluation). -/
private theorem scalarTensorSection_smul (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
    (p : (completedIntegralCommRingSheafUnrestricted l E X).obj.obj U) (x : M.val.obj U) :
    smul l F X ((completedOrdinaryScalarExtension l E F ι X).obj M) U
        ((completedCoefficientMap l E F ι X).hom.app U p)
        (completedScalarTensorSection l E F ι X M U 1 x) =
      completedScalarTensorSection l E F ι X M U 1 (smul l E X M U p x) := by
  obtain ⟨a, ha⟩ := scalarAdjunction l E X F ι
  have h := ((a.unit.app M).val.app U).hom.map_smul p x
  rw [ha, ha] at h
  exact h.symm

/-- Normalized line comparisons multiply the signed pairing by the coefficient map.
Source: Stacks 03EO; blueprint Proof (3), pairing clause of `IsPairNormalized`
(blueprint: lem-pur-completed-line-ordinary-evaluation).
Proof: at zero both lines are the unit comparison and pairing is multiplication; for a
positive exponent this is the pairing clause; for a negative exponent apply that clause
with the two factors interchanged. -/
private theorem pairing_line (L : integralTowerModules l E X)
    [L.IsFiniteLocallyFreeOfRank 1] (N : integralTowerModules l F X)
    [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    (d : PairData l E X F ι L N) (hd : IsPairNormalized l E X F ι L N b d)
    (m : ℤ) (U : X.ProEtᵒᵖ) (p : (power l E X L m).val.obj U)
    (q : (power l E X L (-m)).val.obj U) :
    pairing l F X N m U
        ((d.line m).hom.val.app U
          (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
            (completedCoefficientMap l E F ι X) _ U 1 p))
        ((d.line (-m)).hom.val.app U
          (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
            (completedCoefficientMap l E F ι X) _ U 1 q)) =
      (completedCoefficientMap l E F ι X).hom.app U (pairing l E X L m U p q) := by
  rcases m with (_ | n) | n
  · have h0 : (d.line (Int.ofNat 0)).hom = ((binary l E X F ι).power L 0).hom ≫
        SheafOfModules.scalarTensorPowerMap.{t + 1, t, max u (t + 1)}
          (completedIntegralCommRingSheafUnrestricted l F X) b.hom 0 := hd.1 0
    have h0' : (d.line (-Int.ofNat 0)).hom = ((binary l E X F ι).power L 0).hom ≫
        SheafOfModules.scalarTensorPowerMap.{t + 1, t, max u (t + 1)}
          (completedIntegralCommRingSheafUnrestricted l F X) b.hom 0 := hd.1 0
    have hp (r : (power l E X L (Int.ofNat 0)).val.obj U) :
        (d.line (Int.ofNat 0)).hom.val.app U
          (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
            (completedCoefficientMap l E F ι X) _ U 1 r) =
          (1 * (completedCoefficientMap l E F ι X).hom.app U r :
            (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U) := by
      rw [h0]
      exact SheafOfModules.scalarExtensionUnitIso_tmul (completedCoefficientMap l E F ι X) U 1 r
    have hq (r : (power l E X L (-Int.ofNat 0)).val.obj U) :
        (d.line (-Int.ofNat 0)).hom.val.app U
          (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
            (completedCoefficientMap l E F ι X) _ U 1 r) =
          (1 * (completedCoefficientMap l E F ι X).hom.app U r :
            (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U) := by
      rw [h0']
      exact SheafOfModules.scalarExtensionUnitIso_tmul (completedCoefficientMap l E F ι X) U 1 r
    change (@id ((completedIntegralCommRingSheafUnrestricted l F X).obj.obj U) _) *
        (@id ((completedIntegralCommRingSheafUnrestricted l F X).obj.obj U) _) =
      (completedCoefficientMap l E F ι X).hom.app U
        ((@id ((completedIntegralCommRingSheafUnrestricted l E X).obj.obj U) p) *
          (@id ((completedIntegralCommRingSheafUnrestricted l E X).obj.obj U) q))
    rw [hp, hq]
    have hm : ∀ p' q' : (completedIntegralCommRingSheafUnrestricted l E X).obj.obj U,
        (1 * (completedCoefficientMap l E F ι X).hom.app U p') *
          (1 * (completedCoefficientMap l E F ι X).hom.app U q') =
        (completedCoefficientMap l E F ι X).hom.app U (p' * q') := by
      intro p' q'
      rw [one_mul, one_mul, map_mul]
    exact hm p q
  · have h := hd.2.1 n U 1 1 q p
    rw [one_mul, one_mul] at h
    exact h
  · have h := hd.2.1 n U 1 1 p q
    rw [one_mul, one_mul] at h
    exact h

/-- The ordinary sheaf square: the normalized ordinary comparisons preserve evaluation.
Source: Stacks 03EK, 03EO; blueprint Proof (3)
(blueprint: lem-pur-completed-line-ordinary-evaluation).
Proof: transpose along the scalar-extension adjunction and test on nested pure
tensors `(x ⊗ p) ⊗ q`. The comparisons move the line factors past the scalar, the
evaluation multiplies by the pairing, and `pairing_line` identifies that scalar with
the image of the original pairing. -/
private theorem sheaf_square (L : integralTowerModules l E X)
    [L.IsFiniteLocallyFreeOfRank 1] (N : integralTowerModules l F X)
    [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    (d : PairData l E X F ι L N) (hd : IsPairNormalized l E X F ι L N b d)
    (m : ℤ) (M : integralTowerModules l E X) :
    (d.ordinarySheaf (-m)).hom.app ((sheaf l E X L m).obj M) ≫
      (sheaf l F X N (-m)).map ((d.ordinarySheaf m).hom.app M) ≫
      (evaluation l F X N m).hom.app ((completedOrdinaryScalarExtension l E F ι X).obj M) =
    (completedOrdinaryScalarExtension l E F ι X).map ((evaluation l E X L m).hom.app M) := by
  let : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  obtain ⟨a, ha⟩ := scalarAdjunction l E X F ι
  apply (a.homEquiv _ _).injective
  obtain ⟨_, _, _, hext⟩ := SheafOfModules.tensor_trilinear_universal
    (completedIntegralCommRingSheafUnrestricted l E X)
  apply (hext M (power l E X L m) (power l E X L (-m)) _ _ _).2
  intro U x p q
  let O := completedOrdinaryScalarExtension l E F ι X
  let Z := (sheaf l E X L (-m)).obj ((sheaf l E X L m).obj M)
  let y : Z.val.obj U := tmul l E X L (-m) ((sheaf l E X L m).obj M) U (tmul l E X L m M U x p) q
  have key (T : integralTowerModules l F X) (f : O.obj Z ⟶ T) :
      (a.homEquiv _ _ f).val.app U y =
        f.val.app U (completedScalarTensorSection l E F ι X Z U 1 y) := by
    rw [Adjunction.homEquiv_unit]
    exact congrArg (fun z ↦ f.val.app U z) (ha Z U y)
  change (a.homEquiv _ _ _).val.app U y = (a.homEquiv _ _ _).val.app U y
  rw [key, key]
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  have ha' := hd.2.2.1 (-m) ((sheaf l E X L m).obj M) U 1 (tmul l E X L m M U x p) q
  have hc := hd.2.2.1 m M U 1 x p
  have hevF := (evaluation_existsUnique l F X N m).exists.choose_spec (O.obj M) U
    (completedScalarTensorSection l E F ι X M U 1 x)
    ((d.line m).hom.val.app U
      (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
        (completedCoefficientMap l E F ι X) _ U 1 p))
    ((d.line (-m)).hom.val.app U
      (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
        (completedCoefficientMap l E F ι X) _ U 1 q))
  have hevE := (evaluation_existsUnique l E X L m).exists.choose_spec M U x p q
  have hb := SheafOfModules.map_tmul_first (completedIntegralCommRingSheafUnrestricted l F X)
    ((d.ordinarySheaf m).hom.app M) U
    (completedScalarTensorSection l E F ι X ((sheaf l E X L m).obj M) U 1
      (tmul l E X L m M U x p))
    ((d.line (-m)).hom.val.app U
      (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
        (completedCoefficientMap l E F ι X) _ U 1 q))
  rw [ha']
  erw [hb]
  rw [hc]
  erw [hevF]
  rw [pairing_line l E X F ι L N b d hd m U p q, scalarTensorSection_smul]
  exact (congrArg (completedScalarTensorSection l E F ι X M U 1) hevE.symm).trans
    (completedScalarTensorSection_naturality l E F ι X ((evaluation l E X L m).hom.app M)
      U 1 y).symm

end SheafSquare

section DerivedSquare

/-- Signed evaluation applied termwise to a complex.
Source: Stacks 03EO (blueprint: lem-pur-completed-line-ordinary-evaluation). -/
private def evaluationComplex (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (m : ℤ) (K : CochainComplex (integralTowerModules l E X) ℤ) :
    (complex l E X L (-m)).obj ((complex l E X L m).obj K) ⟶ K where
  f i := (evaluation l E X L m).hom.app (K.X i)
  comm' i j _ := ((evaluation l E X L m).hom.naturality (K.d i j)).symm

/-- The derived evaluation on a representative is the termwise evaluation.
Source: Stacks 06YY, localization of exact functors
(blueprint: lem-pur-completed-line-ordinary-evaluation). -/
private theorem epsilon_app_Q (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (m : ℤ) (K : CochainComplex (integralTowerModules l E X) ℤ) :
    (epsilon l E X L m).hom.app (DerivedCategory.Q.obj K) =
      (tensor l E X L (-m)).map ((factors l E X L m).hom.app K) ≫
        (factors l E X L (-m)).hom.app ((complex l E X L m).obj K) ≫
        DerivedCategory.Q.map (evaluationComplex l E X L m K) := by
  have h1 := Functor.mapDerivedCategoryCompIso_fac (sheaf l E X L m) (sheaf l E X L (-m)) K
  have h2 := Functor.mapDerivedCategoryNatIso_fac (evaluation l E X L m) K
  have h3 := Functor.mapDerivedCategoryIdIso_hom_app_Q_obj K
  have h4 : (Functor.mapHomologicalComplexCompIso
        (Iso.refl (sheaf l E X L m ⋙ sheaf l E X L (-m))) (ComplexShape.up ℤ)).hom.app K ≫
      (NatTrans.mapHomologicalComplex (evaluation l E X L m).hom (ComplexShape.up ℤ)).app K =
      evaluationComplex l E X L m K := by
    apply HomologicalComplex.hom_ext
    intro i
    simp only [evaluationComplex]
    exact Category.id_comp _
  have he : (epsilon l E X L m).hom.app (DerivedCategory.Q.obj K) =
      (Functor.mapDerivedCategoryCompIso (sheaf l E X L m) (sheaf l E X L (-m))).hom.app
          (DerivedCategory.Q.obj K) ≫
        (Functor.mapDerivedCategoryNatIso (evaluation l E X L m)).hom.app
          (DerivedCategory.Q.obj K) ≫
        (Functor.mapDerivedCategoryIdIso (integralTowerModules l E X)).hom.app
          (DerivedCategory.Q.obj K) := rfl
  have h23 : (Functor.mapDerivedCategoryNatIso (evaluation l E X L m)).hom.app
        (DerivedCategory.Q.obj K) ≫
      (Functor.mapDerivedCategoryIdIso (integralTowerModules l E X)).hom.app
        (DerivedCategory.Q.obj K) =
      (sheaf l E X L m ⋙ sheaf l E X L (-m)).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (evaluation l E X L m).hom
          (ComplexShape.up ℤ)).app K) := by
    rw [h3]
    exact h2
  rw [he, h23, ← h1, ← h4]
  erw [Functor.map_comp]
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_app_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
attribute [local semireducible] completedOrdinaryScalarComplex in
/-- Components of the termwise ordinary comparison.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-ordinary-evaluation). -/
private theorem comparisonComplex_hom_f (L : integralTowerModules l E X)
    [L.IsFiniteLocallyFreeOfRank 1] (N : integralTowerModules l F X)
    [N.IsFiniteLocallyFreeOfRank 1] (m : ℤ)
    (e : sheaf l E X L m ⋙ completedOrdinaryScalarExtension l E F ι X ≅
      completedOrdinaryScalarExtension l E F ι X ⋙ sheaf l F X N m)
    (c : CochainComplex (integralTowerModules l E X) ℤ) (i : ℤ) :
    ((comparisonComplex l E X F ι L N m e).hom.app c).f i = e.hom.app (c.X i) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
attribute [local semireducible] completedOrdinaryScalarComplex in
/-- Termwise ordinary comparisons commute with termwise evaluation.
Source: Stacks 03EO (blueprint: lem-pur-completed-line-ordinary-evaluation). -/
private theorem chain_square (L : integralTowerModules l E X)
    [L.IsFiniteLocallyFreeOfRank 1] (N : integralTowerModules l F X)
    [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    (d : PairData l E X F ι L N) (hd : IsPairNormalized l E X F ι L N b d)
    (m : ℤ) (K : CochainComplex (integralTowerModules l E X) ℤ) :
    (comparisonComplex l E X F ι L N (-m) (d.ordinarySheaf (-m))).hom.app
        ((complex l E X L m).obj K) ≫
      (complex l F X N (-m)).map
        ((comparisonComplex l E X F ι L N m (d.ordinarySheaf m)).hom.app K) ≫
      evaluationComplex l F X N m ((completedOrdinaryScalarComplex l E F ι X).obj K) =
    (completedOrdinaryScalarComplex l E F ι X).map (evaluationComplex l E X L m K) := by
  apply HomologicalComplex.hom_ext
  intro i
  simp only [HomologicalComplex.comp_f]
  rw [comparisonComplex_hom_f]
  exact sheaf_square l E X F ι L N b d hd m (K.X i)

set_option backward.isDefEq.respectTransparency false in
attribute [local semireducible] completedScalarCounit completedDerivedScalarExtension
  completedOrdinaryScalarComplex completedOrdinaryScalarExtension completedScalarChangeData in
/-- Naturality of the universal counit for chain maps.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-ordinary-evaluation). -/
private theorem counit_naturality {K K' : CochainComplex (integralTowerModules l E X) ℤ}
    (g : K ⟶ K') :
    (completedDerivedScalarExtension l E F ι X).map (DerivedCategory.Q.map g) ≫
        completedScalarCounit l E F ι X K' =
      completedScalarCounit l E F ι X K ≫
        DerivedCategory.Q.map ((completedOrdinaryScalarComplex l E F ι X).map g) := by
  dsimp only [completedScalarCounit, completedOrdinaryScalarComplex]
  with_unfolding_all
    exact homotopyCounit_naturality (completedOrdinaryScalarExtension l E F ι X)
      (completedDerivedScalarExtension l E F ι X)
      ((completedScalarChangeData l E F ι X).choose_spec.choose_spec.choose_spec
        |>.choose_spec.2.2.choose_spec.choose) g

set_option backward.isDefEq.respectTransparency false in
attribute [local semireducible] completedScalarCounit completedDerivedScalarExtension
  completedOrdinaryScalarComplex completedOrdinaryScalarExtension completedScalarChangeData in
/-- The universal counit is invertible on K-flat complexes.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-ordinary-evaluation). -/
private theorem counit_isIso (K : CochainComplex (integralTowerModules l E X) ℤ)
    (hK : CochainComplex.IsKFlatIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology X)
      (R := completedIntegralCommRingSheafUnrestricted l E X) K) :
    IsIso (completedScalarCounit l E F ι X K) := by
  rw [← completedScalarCochainModel_counit]
  exact (completedScalarCochainModel l E F ι X).computes K hK

/-- Every complex has a good quasi-isomorphic resolution.
Source: Stacks 06YS (blueprint: lem-pur-completed-line-ordinary-evaluation). -/
private theorem good_resolution (c : CochainComplex (integralTowerModules l E X) ℤ) :
    ∃ (P : (integralOperationsGoodComplex l E X).FullSubcategory) (r : P.obj ⟶ c),
      QuasiIso r := by
  obtain ⟨Y, r, hY, hf, hr, -⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients c
  refine ⟨⟨Y, hY, fun n ↦ ?_⟩, r, hr⟩
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso _ (Y.X n)).symm (hf n)


/-- The counit normalization of `IsPairNormalized`, extended from good complexes to all
complexes through good resolutions.
Source: Stacks 06YY and 06YS (blueprint: lem-pur-completed-line-ordinary-evaluation).
Proof: choose a good quasi-isomorphic resolution; every map in the square is natural
for chain maps, and the derived image of the resolution is invertible. -/
private theorem pair_counit (L : integralTowerModules l E X)
    [L.IsFiniteLocallyFreeOfRank 1] (N : integralTowerModules l F X)
    [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    (d : PairData l E X F ι L N) (hd : IsPairNormalized l E X F ι L N b d)
    (m : ℤ) (c : CochainComplex (integralTowerModules l E X) ℤ) :
    (completedDerivedScalarExtension l E F ι X).map ((factors l E X L m).hom.app c) ≫
        completedScalarCounit l E F ι X ((complex l E X L m).obj c) ≫
        DerivedCategory.Q.map
          ((comparisonComplex l E X F ι L N m (d.ordinarySheaf m)).hom.app c) =
      (d.ordinary m).hom.app (DerivedCategory.Q.obj c) ≫
        (tensor l F X N m).map (completedScalarCounit l E F ι X c) ≫
        (factors l F X N m).hom.app ((completedOrdinaryScalarComplex l E F ι X).obj c) := by
  obtain ⟨P, r, hr⟩ := good_resolution l E X c
  have hP := eq_of_heq (hd.2.2.2 m P)
  have : IsIso (DerivedCategory.Q.map r) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hr
  let C := completedDerivedScalarExtension l E F ι X
  let κ := completedScalarCounit l E F ι X
  let O := completedOrdinaryScalarComplex l E F ι X
  let Q := DerivedCategory.Q (C := integralTowerModules l E X)
  let Q' := DerivedCategory.Q (C := integralTowerModules l F X)
  rw [← cancel_epi (C.map ((tensor l E X L m).map (Q.map r)))]
  have n1 : (tensor l E X L m).map (Q.map r) ≫ (factors l E X L m).hom.app c =
      (factors l E X L m).hom.app P.obj ≫ Q.map ((complex l E X L m).map r) :=
    (factors l E X L m).hom.naturality r
  have n2 : C.map (Q.map ((complex l E X L m).map r)) ≫ κ ((complex l E X L m).obj c) =
      κ ((complex l E X L m).obj P.obj) ≫ Q'.map (O.map ((complex l E X L m).map r)) :=
    counit_naturality l E X F ι ((complex l E X L m).map r)
  have n3 : O.map ((complex l E X L m).map r) ≫
      (comparisonComplex l E X F ι L N m (d.ordinarySheaf m)).hom.app c =
      (comparisonComplex l E X F ι L N m (d.ordinarySheaf m)).hom.app P.obj ≫
        (complex l F X N m).map (O.map r) :=
    (comparisonComplex l E X F ι L N m (d.ordinarySheaf m)).hom.naturality r
  have n4 : C.map ((tensor l E X L m).map (Q.map r)) ≫ (d.ordinary m).hom.app (Q.obj c) =
      (d.ordinary m).hom.app (Q.obj P.obj) ≫ (tensor l F X N m).map (C.map (Q.map r)) :=
    (d.ordinary m).hom.naturality (Q.map r)
  have n5 : C.map (Q.map r) ≫ κ c = κ P.obj ≫ Q'.map (O.map r) :=
    counit_naturality l E X F ι r
  have n6 : (tensor l F X N m).map (Q'.map (O.map r)) ≫ (factors l F X N m).hom.app (O.obj c) =
      (factors l F X N m).hom.app (O.obj P.obj) ≫ Q'.map ((complex l F X N m).map (O.map r)) :=
    (factors l F X N m).hom.naturality (O.map r)
  have lhs : C.map ((tensor l E X L m).map (Q.map r)) ≫ C.map ((factors l E X L m).hom.app c) ≫
      κ ((complex l E X L m).obj c) ≫
        Q'.map ((comparisonComplex l E X F ι L N m (d.ordinarySheaf m)).hom.app c) =
      (C.map ((factors l E X L m).hom.app P.obj) ≫ κ ((complex l E X L m).obj P.obj) ≫
        Q'.map ((comparisonComplex l E X F ι L N m (d.ordinarySheaf m)).hom.app P.obj)) ≫
        Q'.map ((complex l F X N m).map (O.map r)) := by
    rw [← Functor.map_comp_assoc, n1, Functor.map_comp, Category.assoc, reassoc_of% n2,
      ← Functor.map_comp, n3, Functor.map_comp]
    simp only [Category.assoc]
  have rhs : C.map ((tensor l E X L m).map (Q.map r)) ≫ (d.ordinary m).hom.app (Q.obj c) ≫
      (tensor l F X N m).map (κ c) ≫ (factors l F X N m).hom.app (O.obj c) =
      ((d.ordinary m).hom.app (Q.obj P.obj) ≫ (tensor l F X N m).map (κ P.obj) ≫
        (factors l F X N m).hom.app (O.obj P.obj)) ≫
        Q'.map ((complex l F X N m).map (O.map r)) := by
    rw [reassoc_of% n4, ← Functor.map_comp_assoc, n5, Functor.map_comp, Category.assoc, n6]
    simp only [Category.assoc]
  refine lhs.trans (Eq.trans ?_ rhs.symm)
  exact congrArg (fun z ↦ z ≫ Q'.map ((complex l F X N m).map (O.map r))) hP
end DerivedSquare

/-- The ordinary scalar comparison respects the specified signed-line evaluation.
Source: Stacks 03EL, 03EO, 06YY; blueprint Proof (3), inverse-pair compatibility
(blueprint: lem-pur-completed-line-ordinary-evaluation).
Proof: first check the ordinary sheaf square on sections. The two scalar-line
comparisons move the two line factors past the scalar factor. Evaluation then
multiplies by the image of their pairing. For positive exponents this is precisely
IsPairNormalized's negative pairing clause; for negative exponents interchange the
paired factors, and for zero use multiplication. The defining evaluation formula
identifies the other path with scalar extension of evaluation. Sheafified tensor
generators determine these maps. Apply the square termwise to a flat-term K-flat
representative. Exact line tensor preserves these representatives. Substitute the
universal-counit normalizations of the two ordinary comparisons and the exact
localization comparisons of evaluation. Naturality and cancellation of the invertible
K-flat counits give the derived square. Every derived object has such a resolution,
so naturality transports the equality to every unbounded object. This argument uses
ordinary derived extension only, with no completeness assumption. -/
theorem ordinary_evaluation_compatibility (L : integralTowerModules l E X)
    [L.IsFiniteLocallyFreeOfRank 1] (N : integralTowerModules l F X)
    [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    (d : PairData l E X F ι L N) (hd : IsPairNormalized l E X F ι L N b d)
    (m : ℤ) (K : DerivedCategory (integralTowerModules l E X)) :
    (d.ordinary (-m)).hom.app ((tensor l E X L m).obj K) ≫
      (tensor l F X N (-m)).map
        ((d.ordinary m).hom.app K) ≫
      (epsilon l F X N m).hom.app ((completedDerivedScalarExtension l E F ι X).obj K) =
    (completedDerivedScalarExtension l E F ι X).map
      ((epsilon l E X L m).hom.app K) := by
  classical
  let C := completedDerivedScalarExtension l E F ι X
  let κ := completedScalarCounit l E F ι X
  let O := completedOrdinaryScalarComplex l E F ι X
  let T := tensor l E X L
  let T' := tensor l F X N
  let Q := DerivedCategory.Q (C := integralTowerModules l E X)
  let Q' := DerivedCategory.Q (C := integralTowerModules l F X)
  have hgood : ∀ c : CochainComplex (integralTowerModules l E X) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients
        (J := AlgebraicGeometry.Scheme.ProEt.topology X)
        (R := completedIntegralCommRingSheafUnrestricted l E X) c →
      (d.ordinary (-m)).hom.app ((T m).obj (Q.obj c)) ≫
        (T' (-m)).map ((d.ordinary m).hom.app (Q.obj c)) ≫
        (epsilon l F X N m).hom.app (C.obj (Q.obj c)) =
      C.map ((epsilon l E X L m).hom.app (Q.obj c)) := by
    intro c hc
    have := counit_isIso l E X F ι c hc
    rw [← cancel_mono (κ c)]
    symm
    rw [epsilon_app_Q l E X L m c]
    simp only [Functor.map_comp, Category.assoc]
    rw [counit_naturality l E X F ι (evaluationComplex l E X L m c),
      ← chain_square l E X F ι L N b d hd m c]
    simp only [Functor.map_comp]
    rw [reassoc_of% (pair_counit l E X F ι L N b d hd (-m) ((complex l E X L m).obj c))]
    have nf : (factors l F X N (-m)).hom.app (O.obj ((complex l E X L m).obj c)) ≫
        Q'.map ((complex l F X N (-m)).map
          ((comparisonComplex l E X F ι L N m (d.ordinarySheaf m)).hom.app c)) =
        (T' (-m)).map (Q'.map
          ((comparisonComplex l E X F ι L N m (d.ordinarySheaf m)).hom.app c)) ≫
          (factors l F X N (-m)).hom.app ((complex l F X N m).obj (O.obj c)) :=
      ((factors l F X N (-m)).hom.naturality _).symm
    rw [reassoc_of% nf]
    have nΩ : C.map ((T (-m)).map ((factors l E X L m).hom.app c)) ≫
        (d.ordinary (-m)).hom.app (Q.obj ((complex l E X L m).obj c)) =
        (d.ordinary (-m)).hom.app ((T m).obj (Q.obj c)) ≫
          (T' (-m)).map (C.map ((factors l E X L m).hom.app c)) :=
      (d.ordinary (-m)).hom.naturality _
    rw [reassoc_of% nΩ]
    have hm : (T' (-m)).map (C.map ((factors l E X L m).hom.app c)) ≫
        (T' (-m)).map (κ ((complex l E X L m).obj c)) ≫
        (T' (-m)).map (Q'.map
          ((comparisonComplex l E X F ι L N m (d.ordinarySheaf m)).hom.app c)) =
        (T' (-m)).map ((d.ordinary m).hom.app (Q.obj c)) ≫
          (T' (-m)).map ((T' m).map (κ c)) ≫
          (T' (-m)).map ((factors l F X N m).hom.app (O.obj c)) := by
      simp only [← Functor.map_comp]
      rw [pair_counit l E X F ι L N b d hd m c]
    rw [reassoc_of% hm]
    have hε2 : (T' (-m)).map ((factors l F X N m).hom.app (O.obj c)) ≫
        (factors l F X N (-m)).hom.app ((complex l F X N m).obj (O.obj c)) ≫
        Q'.map (evaluationComplex l F X N m (O.obj c)) =
        (epsilon l F X N m).hom.app (Q'.obj (O.obj c)) :=
      (epsilon_app_Q l F X N m (O.obj c)).symm
    rw [hε2]
    have hn : (T' (-m)).map ((T' m).map (κ c)) ≫ (epsilon l F X N m).hom.app (Q'.obj (O.obj c)) =
        (epsilon l F X N m).hom.app (C.obj (Q.obj c)) ≫ κ c :=
      (epsilon l F X N m).hom.naturality (κ c)
    rw [hn]
  have hloc := integralOperationsGoodLocalization_isLocalization l E X
  have hess : (integralOperationsGoodLocalization l E X).EssSurj :=
    Localization.essSurj _ ((HomologicalComplex.quasiIso (integralTowerModules l E X)
      (.up ℤ)).inverseImage (integralOperationsGoodComplex l E X).ι)
  let P := (integralOperationsGoodLocalization l E X).objPreimage K
  let e : DerivedCategory.Q.obj P.obj ≅ K :=
    (integralOperationsGoodLocalization l E X).objObjPreimageIso K
  have h := hgood P.obj P.property.1
  simp only [C, T, T', Q] at h
  rw [← cancel_epi ((completedDerivedScalarExtension l E F ι X).map
    ((tensor l E X L (-m)).map ((tensor l E X L m).map e.hom)))]
  have n1 : (completedDerivedScalarExtension l E F ι X).map
        ((tensor l E X L (-m)).map ((tensor l E X L m).map e.hom)) ≫
      (d.ordinary (-m)).hom.app ((tensor l E X L m).obj K) =
      (d.ordinary (-m)).hom.app ((tensor l E X L m).obj (DerivedCategory.Q.obj P.obj)) ≫
        (tensor l F X N (-m)).map ((completedDerivedScalarExtension l E F ι X).map
          ((tensor l E X L m).map e.hom)) :=
    (d.ordinary (-m)).hom.naturality _
  have n2 : (completedDerivedScalarExtension l E F ι X).map ((tensor l E X L m).map e.hom) ≫
      (d.ordinary m).hom.app K =
      (d.ordinary m).hom.app (DerivedCategory.Q.obj P.obj) ≫
        (tensor l F X N m).map ((completedDerivedScalarExtension l E F ι X).map e.hom) :=
    (d.ordinary m).hom.naturality _
  have n3 : (tensor l F X N (-m)).map ((tensor l F X N m).map
        ((completedDerivedScalarExtension l E F ι X).map e.hom)) ≫
      (epsilon l F X N m).hom.app ((completedDerivedScalarExtension l E F ι X).obj K) =
      (epsilon l F X N m).hom.app ((completedDerivedScalarExtension l E F ι X).obj
        (DerivedCategory.Q.obj P.obj)) ≫ (completedDerivedScalarExtension l E F ι X).map e.hom :=
    (epsilon l F X N m).hom.naturality _
  have n4 : (tensor l E X L (-m)).map ((tensor l E X L m).map e.hom) ≫
      (epsilon l E X L m).hom.app K =
      (epsilon l E X L m).hom.app (DerivedCategory.Q.obj P.obj) ≫ e.hom :=
    (epsilon l E X L m).hom.naturality _
  rw [reassoc_of% n1, ← Functor.map_comp_assoc, n2, Functor.map_comp, Category.assoc,
    n3, ← Functor.map_comp, n4, Functor.map_comp, ← reassoc_of% h]

end CompletedLineTensor
end WeilConjectures
