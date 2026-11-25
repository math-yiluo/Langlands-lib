/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ShriekTraceFunctionFiniteEtale
public import WeilConjectures.ZetaFunction.WeilObjectOfLisseTraceFunction

/-!
# The local traces of the Weil object of a lisse sheaf as Galois traces

For a lisse `ℓ`-adic sheaf `H` on `X₀`, `b ∈ ℚ̄_ℓˣ` and an `𝔽_{q^{n+1}}`-point `y` of `X₀` with
geometric point `x̄ = Spec ι ≫ y`, the local trace of the Weil object `(H, b)` at `x̄`, read in
`ℚ̄_ℓ`, is `b^{n+1}` times the trace of the Galois action of `σ^{n+1}` on the global sections
`Γ(Spec k̄, x̄^* H)` of the model of the `ℓ`-adic sheaves
(`WeilComplex.endTensorUnitRingEquiv_weilStalkTraceAlternatingSum_weilObjectOfLisse_eq`); on
the side of the Weil sheaf `p^* H`, its trace function is the same Galois trace
(`WeilSheaf.traceFunction_geometricFiberPullback_eq_trace`).
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor Limits

open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.WeilComplex

open ProEtale ProEtale.CondensedRing

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

attribute [local instance] fact_ringChar_prime_of_finite

omit [Fact (ringChar k₀ ≠ l)] in
/-- The powers of the image of a scalar multiplication of `ℓ`-adic sheaves under a functor. -/
lemma pow_map_adicSheafSmul {D : Type*} [Category D] {Z : Scheme.{u}} (F : AdicSheaf l Z ⥤ D)
    (c : PadicAlgCl l) (M : AdicSheaf l Z) (n : ℕ) :
    (End.of (F.map (AdicSheaf.smul (ULift.up c) M)) ^ n).asHom =
      F.map (AdicSheaf.smul (ULift.up (c ^ n)) M) := by
  induction n with
  | zero =>
    rw [_root_.pow_zero, _root_.pow_zero]
    erw [AdicSheaf.smul_one, CategoryTheory.Functor.map_id]
    rfl
  | succ n ih =>
    rw [_root_.pow_succ, End.mul_asHom, ih, ← F.map_comp, AdicSheaf.smul_smul, _root_.pow_succ]
    rfl

omit [Fact (ringChar k₀ ≠ l)] in
/-- The powers of the image of the multiplication by `b ∈ ℚ̄_ℓˣ` under a functor. -/
lemma pow_map_smulIso_hom {D : Type*} [Category D] {Z : Scheme.{u}} (F : AdicSheaf l Z ⥤ D)
    (b : (PadicAlgCl l)ˣ) (M : AdicSheaf l Z) (n : ℕ) :
    (End.of (F.map (WeilCoefficients.smulIso b M).hom) ^ n).asHom =
      F.map (AdicSheaf.smul (ULift.up ((b : PadicAlgCl l) ^ n)) M) :=
  pow_map_adicSheafSmul F (b : PadicAlgCl l) M n

omit [Fact (ringChar k₀ ≠ l)] in
/-- The stalk Frobenius at a point `x̄` fixed by `σ` of a module object with the morphism
`(𝟙)^* ≅ 𝟭` followed by an endomorphism `γ` is the Galois action
`x̄^* M ⟶ σ^* x̄^* M ≅ (σ ≫ x̄)^* M = x̄^* M` followed by `x̄^* γ`. -/
lemma stalkFrobenius_upperStarIsoIdOfEq_comp {k : Type u} [Field k]
    {Z : Over (Spec (.of k))} {e : Z ≅ Z} (he : e.hom.left = 𝟙 Z.left) {P : Scheme.{u}}
    {σ : P ⟶ P} (τ : (σ)^*⟦Profinite.padicAlgClRingObj l⟧ ≅ 𝟭 _) {x : P ⟶ Z.left}
    (hx : x ≫ e.hom.left = σ ≫ x) (h : σ ≫ x = x)
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) Z.left)) (γ : M ⟶ M) :
    stalkFrobenius l τ e hx ((upperStarIsoIdOfEq l he).hom.app M ≫ γ) =
      τ.inv.app ((x)^*⟦Profinite.padicAlgClRingObj l⟧.obj M) ≫
        (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) σ x).inv.app M ≫
        (CondensedRing.upperStarEqToIso (Profinite.padicAlgClRingObj l) h).hom.app M ≫
        (x)^*⟦Profinite.padicAlgClRingObj l⟧.map γ := by
  rw [stalkFrobenius, weilPointComparison_eq_pointComparison, pointComparison_hom_app,
    upperStarCongr_hom_app_eq_eqToHom, Functor.map_comp, Category.assoc, Category.assoc,
    Category.assoc,
    reassoc_of% (upperStarComp_hom_app_comp_map_upperStarIsoIdOfEq_hom_app l x he M),
    ← upperStarEqToIso_hom_app (Profinite.padicAlgClRingObj l) hx.symm,
    upperStarEqToIso_hom_app_trans_assoc]

omit [Fact (ringChar k₀ ≠ l)] in
/-- `AlgebraicGeometry.ProEtale.endTensorUnitRingEquiv_traceOrZero_galoisUpperStarEnd` for the
`n`-th power of the multiplication by `b ∈ ℚ̄_ℓˣ`. -/
lemma endTensorUnitRingEquiv_traceOrZero_galoisUpperStarEnd_pow_smulIso {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] {Y : Scheme.{u}} (σ : Spec (.of Ω) ⟶ Spec (.of Ω)) (x : Spec (.of Ω) ⟶ Y)
    (h : σ ≫ x = x) (τ : (σ)^*⟦Profinite.padicAlgClRingObj l⟧ ≅ 𝟭 _)
    (hτ : τ.inv.app 𝟙ₘ = (Functor.Monoidal.εIso (σ)^*⟦Profinite.padicAlgClRingObj l⟧).hom)
    (H : AdicSheaf l Y) {r : ℕ}
    (eH : (x)^*ᵃ[l].obj H ≅ ⨁ fun _ : Fin r ↦ AdicSheaf.unit l (Spec (.of Ω)))
    (b : (PadicAlgCl l)ˣ) (n : ℕ) :
    CondensedRing.endTensorUnitRingEquiv l Ω (traceOrZero
      (galoisUpperStarEnd σ x h τ ((adicSheafEquivCondensedMod l Y).functor.obj H)
          (End.of
            ((adicSheafEquivCondensedMod l Y).functor.mapIso (WeilCoefficients.smulIso b H)).hom ^
            n).asHom)) =
      (b : PadicAlgCl l) ^ n * LinearMap.trace (PadicAlgCl l) _
        ((WeilCoefficients.toModuleCat l).map (galoisGlobalSections σ x h H)).hom := by
  rw [Functor.mapIso_hom, pow_map_smulIso_hom]
  exact endTensorUnitRingEquiv_traceOrZero_galoisUpperStarEnd σ x h τ hτ H eH _

omit [Fact (ringChar k₀ ≠ l)] in
/-- The trace of the stalk Frobenius at a geometric point `x̄` fixed by `σ` of the `(n + 1)`-st
power of the Weil sheaf `(H, (𝟙)^* ≅ 𝟭 ≫ b)` for an automorphism `e` with `e.hom.left = 𝟙`, read
in `ℚ̄_ℓ`, is `b^{n+1}` times the trace of the Galois action on the global sections of
`x̄^* H`. -/
lemma endTensorUnitRingEquiv_stalkFrobeniusTrace_pow_mk_smulIso {k : Type u} [Field k]
    {Y : Over (Spec (.of k))} {e : Y ≅ Y} (he : e.hom.left = 𝟙 Y.left) (H : AdicSheaf l Y.left)
    (b : (PadicAlgCl l)ˣ) (n : ℕ) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (σ : Spec (.of Ω) ⟶ Spec (.of Ω)) (τ : (σ)^*⟦Profinite.padicAlgClRingObj l⟧ ≅ 𝟭 _)
    (hτ : τ.inv.app 𝟙ₘ = (Functor.Monoidal.εIso (σ)^*⟦Profinite.padicAlgClRingObj l⟧).hom)
    (x : Spec (.of Ω) ⟶ Y.left) (hx : x ≫ (e.pow (n + 1)).hom.left = σ ≫ x) (h : σ ≫ x = x)
    {r : ℕ} (eH : (x)^*ᵃ[l].obj H ≅ ⨁ fun _ : Fin r ↦ AdicSheaf.unit l (Spec (.of Ω))) :
    CondensedRing.endTensorUnitRingEquiv l Ω (stalkFrobeniusTrace l τ (e.pow (n + 1)) hx
      (CondensedRing.WeilSheaf.pow l (IsoAlgebra.mk
        ((adicSheafEquivCondensedMod l Y.left).functor.obj H)
        ((upperStarIsoIdOfEq l he).app _ ≪≫
          (adicSheafEquivCondensedMod l Y.left).functor.mapIso
            (WeilCoefficients.smulIso b H)) : CondensedRing.WeilSheaf l e) (n + 1)).str.hom) =
      (b : PadicAlgCl l) ^ (n + 1) * LinearMap.trace (PadicAlgCl l) _
        ((WeilCoefficients.toModuleCat l).map (galoisGlobalSections σ x h H)).hom := by
  rw [WeilSheaf.pow_mk_upperStarIsoIdOfEq_str_hom, stalkFrobeniusTrace_eq]
  erw [stalkFrobenius_upperStarIsoIdOfEq_comp (pow_hom_left_eq_id he (n + 1)) τ hx h]
  rw [galoisUpperStarEnd_eq_comp]
  exact endTensorUnitRingEquiv_traceOrZero_galoisUpperStarEnd_pow_smulIso σ x h τ hτ H eH b
    (n + 1)

/-- The pullback of a lisse `ℓ`-adic sheaf to a separably closed point is constant: a finite
direct sum of copies of `ℚ̄_ℓ`. -/
theorem _root_.AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.exists_upperStar_iso_biproduct_unit
    {Y : Scheme.{u}} {H : AdicSheaf l Y} (hH : IsAdicLisseSheaf H) {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ Y) :
    ∃ r : ℕ, Nonempty ((x)^*ᵃ[l].obj H ≅ ⨁ fun _ : Fin r ↦ AdicSheaf.unit l (Spec (.of Ω))) := by
  have := IsStrictlyHenselianLocalRing.of_isSepClosed Ω
  exact (hH.upperStar x).exists_iso_biproduct_unit_of_isStrictlyHenselian

/-- **The local traces of the Weil object of a lisse sheaf as Galois traces**: the local trace of
the Weil object `(H, b)` at the geometric point `x̄` of an `𝔽_{q^{n+1}}`-point, read in `ℚ̄_ℓ`, is
`b^{n+1}` times the trace of the Galois action of `σ^{n+1}` on `Γ(Spec k̄, x̄^* H)`. -/
theorem endTensorUnitRingEquiv_weilStalkTraceAlternatingSum_weilObjectOfLisse_eq
    {H : AdicSheaf l X} (hH : IsAdicLisseSheaf H) (b : (PadicAlgCl l)ˣ) (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ (n + 1))) :
    endTensorUnitRingEquiv l (AlgebraicClosure k₀)
        (weilStalkTraceAlternatingSum l (n + 1) _
          (frobeniusFixedPointsReflOfFieldPoint (X := overSpec X) n y).2.2
          (weilObjectOfLisse (k₀ := k₀) hH b)) =
      (b : PadicAlgCl l) ^ (n + 1) * LinearMap.trace (PadicAlgCl l) _
        ((WeilCoefficients.toModuleCat l).map (galoisGlobalSections
          ((geometricFrobeniusField k₀).pow (n + 1)).hom
          (frobeniusFixedPointsReflOfFieldPoint (X := overSpec X) n y).1
          (frobeniusFixedPointsReflOfFieldPoint_fixed n y) H)).hom := by
  have hK0 : (weilObjectOfLisse (k₀ := k₀) hH b).str =
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj.{u} l) l _).app
        (weilObjectOfLisse (k₀ := k₀) hH b).carrier ≪≫ boundedConstructibleOfLisseSMulIso hH b :=
    IsoAlgebra.mk_str _ _
  have hK := congrArg Iso.hom hK0
  rw [Iso.trans_hom, Iso.app_hom] at hK
  rw [weilStalkTraceAlternatingSum_eq_traceOrZero_of_homology l _ _ hK (fun j hj ↦ ?_)
    ((adicSheafEquivCondensedMod l (overSpec (k₀ := k₀) X).left).functor.obj H)
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app
      ((adicSheafEquivCondensedMod l X).functor.obj H))
    ((adicSheafEquivCondensedMod l (overSpec (k₀ := k₀) X).left).functor.mapIso
      (WeilCoefficients.smulIso (Z := (overSpec (k₀ := k₀) X).left) b H))
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom.naturality
      ((adicSheafEquivCondensedMod l X).functor.map (WeilCoefficients.smulIso b H).hom))]
  · obtain ⟨r, ⟨eH⟩⟩ := hH.exists_upperStar_iso_biproduct_unit
      (Ω := AlgebraicClosure k₀) (frobeniusFixedPointsReflOfFieldPoint (X := overSpec X) n y).1
    have hτ := upperStarIsoIdOfIsSepClosed_inv_app_tensorUnit l
      ((geometricFrobeniusField k₀).pow (n + 1)).hom
    rw [weilSheafStalkTrace_eq_stalkFrobeniusTrace]
    generalize upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l)
      ((geometricFrobeniusField k₀).pow (n + 1)).hom = τ at hτ ⊢
    exact endTensorUnitRingEquiv_stalkFrobeniusTrace_pow_mk_smulIso (Y := overSpec X)
      (e := Iso.refl _) _ H b n ((geometricFrobeniusField k₀).pow (n + 1)).hom τ hτ
      (frobeniusFixedPointsReflOfFieldPoint (X := overSpec X) n y).1 _
      (frobeniusFixedPointsReflOfFieldPoint_fixed n y) eH
  · obtain hj | hj := lt_or_gt_of_ne hj
    · exact ((DerivedCategory.singleFunctor _ 0).obj
        ((adicSheafEquivCondensedMod l X).functor.obj H)).isZero_of_isGE 0 j hj
    · exact ((DerivedCategory.singleFunctor _ 0).obj
        ((adicSheafEquivCondensedMod l X).functor.obj H)).isZero_of_isLE 0 j hj

end AlgebraicGeometry.WeilComplex
