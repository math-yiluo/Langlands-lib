/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.BifunctorHomBidual
public import WeilConjectures.WeilSheaf.DerivedHomConstructible
public import WeilConjectures.WeilSheaf.IhomCurry
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
public import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryBiduality
public import WeilConjectures.WeilSheaf.UpperShriekGeometric
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.CategoryTheory.RingedForgetTwoInjective.RingedForgetTwoInjectiveModels
import WeilConjectures.WeilSheaf.DerivedHomPrecomposition

/-!
# Verdier biduality for Weil complexes

Let `X` be a separated `k₀`-scheme of finite type and `W` a Weil complex on `X`. The derived
internal hom into `W` is a duality `D_W = RHom(-, W)` on Weil complexes
(`AlgebraicGeometry.WeilComplex.dual`, by
`AlgebraicGeometry.WeilComplex.objectProperty_derivedHom`).
This file constructs the double-dual natural transformation `𝟭 ⟶ D_W D_W`
(`AlgebraicGeometry.WeilComplex.toDualDual`) and shows that it is an isomorphism when the
underlying `ℓ`-adic complex of `W` on the geometric fibre `X̄` is the dualizing complex of `X̄`
(`AlgebraicGeometry.WeilComplex.nonempty_iso_dual_rightOp_comp_dual`). This is Verdier biduality
for Weil complexes (blueprint: `theorem-verdier-biduality`).

## Construction

* The biduality morphisms `A ⟶ [[A, B], B]` of pro-étale Weil sheaves
  (`AlgebraicGeometry.ProEtaleWeilSheaf.bidual`) are those of the underlying `ℓ`-adic sheaves,
  which are compatible with the Weil structures; they form an evaluation for the internal hom
  (`AlgebraicGeometry.ProEtaleWeilSheaf.bifunctorEvaluation`).
* The double-dual morphisms of hom complexes then descend to the derived category
  (`DerivedCategory.bifunctorRHomBidual`), giving `toDualDual`.

## Proof of biduality

Forgetting the Weil structure reflects isomorphisms. It carries the double-dual morphism of hom
complexes of pro-étale Weil sheaves to that of `ℓ`-adic sheaves
(`CochainComplex.map_bifunctorHomBidual`), which is a quasi-isomorphism on bounded constructible
complexes when the target represents the dualizing complex of `X̄`
(`AlgebraicGeometry.ProEtaleWeilSheaf.quasiIso_bifunctorHomBidual_ordinary`).

## The dualizing complex

The underlying complex on `X̄` of `Ra_X^! ℚ̄_ℓ`, for the exceptional inverse image of Weil
complexes, is the dualizing complex of `X̄`
(`AlgebraicGeometry.WeilComplex.nonempty_nativeGeometricForget_obj_iso_of_adjunction`, blueprint
`prose-10-20`, in `WeilConjectures.WeilSheaf.UpperShriekGeometric`).

The constructible biduality of hom complexes of `ℓ`-adic sheaves
(`AlgebraicGeometry.ProEtaleWeilSheaf.quasiIso_bifunctorHomBidual_ordinary`) is read off from the
condensed biduality `ProEtale.CondensedRing.isIso_verdierBiduality`.
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Category Limits Opposite MonoidalCategory Functor.LaxMonoidal

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace ProEtaleWeilSheaf

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

omit [Fact (ringChar k₀ ≠ l)] in
/-- The uncurried form of the biduality morphism `A ⟶ [[A, B], B]` is compatible with the Weil
structures. -/
lemma bidual_uncurry_str (A B : ProEtaleWeilSheaf k₀ l X) :
    (A.str.hom.hom ⊗ₘ (ProEtaleWeilSheaf.ihom k₀ l X A B).str.hom.hom) ≫
        ((Mod.bidual A.carrier B.carrier).hom ▷ (ProEtaleWeilSheaf.ihom k₀ l X A B).carrier.X ≫
          Mod.evaluation (ProEtaleWeilSheaf.ihom k₀ l X A B).carrier B.carrier) =
      μ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[
          WeilCoefficients.{u} l] A.carrier.X (ProEtaleWeilSheaf.ihom k₀ l X A B).carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[_].map
          ((Mod.bidual A.carrier B.carrier).hom ▷ (ProEtaleWeilSheaf.ihom k₀ l X A B).carrier.X ≫
            Mod.evaluation (ProEtaleWeilSheaf.ihom k₀ l X A B).carrier B.carrier) ≫
        B.str.hom.hom := by
  have hb : (Mod.bidual A.carrier B.carrier).hom ▷ (ProEtaleWeilSheaf.ihom k₀ l X A B).carrier.X ≫
      Mod.evaluation (ProEtaleWeilSheaf.ihom k₀ l X A B).carrier B.carrier =
      (β_ A.carrier.X (ProEtaleWeilSheaf.ihom k₀ l X A B).carrier.X).hom ≫
        Mod.evaluation A.carrier B.carrier :=
    Mod.uncurryHom_bidual A.carrier B.carrier
  rw [hb, BraidedCategory.braiding_naturality_assoc, ihom_evaluation_str, Functor.map_comp,
    assoc, Functor.LaxBraided.braided_assoc]
  rfl

/-- The biduality morphism `A ⟶ [[A, B], B]` of pro-étale Weil sheaves: the biduality morphism
of the underlying `ℓ`-adic sheaves. -/
noncomputable def bidual (A B : ProEtaleWeilSheaf k₀ l X) :
    A ⟶ ProEtaleWeilSheaf.ihom k₀ l X (ProEtaleWeilSheaf.ihom k₀ l X A B) B :=
  homToIhom A (ProEtaleWeilSheaf.ihom k₀ l X A B) B (Mod.bidual A.carrier B.carrier)
    (bidual_uncurry_str A B)

omit [Fact (ringChar k₀ ≠ l)] in
@[simp]
lemma bidual_hom_f (A B : ProEtaleWeilSheaf k₀ l X) :
    (bidual A B).hom.f = Mod.bidual A.carrier B.carrier :=
  rfl

variable (k₀ l X)

/-- The biduality morphisms of pro-étale Weil sheaves, as an evaluation for the internal hom. -/
noncomputable def bifunctorEvaluation :
    CochainComplex.BifunctorEvaluation (ihomBifunctor k₀ l X) where
  ev A B := bidual A B
  naturality f B := ObjectProperty.hom_ext _
    (Endofunctor.Algebra.Hom.ext (Mod.bidual_naturality f.hom.f B.carrier))
  dinaturality A _ _ g := ObjectProperty.hom_ext _
    (Endofunctor.Algebra.Hom.ext (Mod.bidual_comp_ihom_map A.carrier g.hom.f))

instance (J : Type) : PreservesLimitsOfShape (Discrete J)
    (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) := by
  let A := ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  have : HasColimitsOfSize.{u + 1, u + 1} A := inferInstance
  have : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} A
  exact (Endofunctor.IsoAlgebra.Free.adjunction
    (WeilSheaf.frobeniusPullback k₀ l X)).rightAdjoint_preservesLimits.preservesLimitsOfShape

/-- Forgetting the Weil structure commutes with the internal homs. -/
noncomputable def ihomBifunctorMapIso :
    CochainComplex.BifunctorMapIso (ihomBifunctor k₀ l X)
      (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) where
  iso _ _ := Iso.refl _
  naturality_left _ _ := by
    simp only [Iso.refl_hom, comp_id, id_comp]
    rfl
  naturality_right _ _ _ _ := by
    simp only [Iso.refl_hom, comp_id, id_comp]
    rfl

lemma bifunctorEvaluation_mapCompatible :
    (bifunctorEvaluation k₀ l X).MapCompatible (ihomBifunctorMapIso k₀ l X)
      (ordinaryBifunctorEvaluation l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) := by
  intro A B
  change _ ≫ 𝟙 _ ≫ ((ordinaryIhomBifunctor _ _).map (𝟙 _).op).app _ = _
  rw [op_id, CategoryTheory.Functor.map_id, NatTrans.id_app, id_comp, comp_id]
  rfl

/-- Precomposition with quasi-isomorphisms is a quasi-isomorphism of hom complexes into a
K-injective complex of pro-étale Weil sheaves. -/
lemma precompQuasiIso (I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) [I.IsKInjective] :
    DerivedCategory.PrecompQuasiIso
      (ihomBifunctor k₀ l X) I :=
  fun _ _ a _ ↦ quasiIso_bifunctorHomMapLeft a

end ProEtaleWeilSheaf

namespace WeilComplex

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

variable (X) in
/-- The geometric fibre `X̄` of `X`, as a scheme over the algebraic closure `k̄` of `k₀`. -/
noncomputable abbrev geometricFiberOver : Over (Spec (.of (AlgebraicClosure k₀))) :=
  Over.mk (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure

variable (W : WeilComplex k₀ l X)

/-- The duality `D_W = RHom(-, W)` of Weil complexes into a Weil complex `W`. -/
noncomputable def dual : (WeilComplex k₀ l X)ᵒᵖ ⥤ WeilComplex k₀ l X :=
  ObjectProperty.lift _
    ((ObjectProperty.ι _).op ⋙ ProEtaleWeilSheaf.derivedHom k₀ l X W.obj)
    fun K ↦ objectProperty_derivedHom K.unop W

/-- The double-dual morphism `K ⟶ D_W D_W K` of Weil complexes. -/
noncomputable def toDualDual : 𝟭 (WeilComplex k₀ l X) ⟶ (dual W).rightOp ⋙ dual W where
  app K := ObjectProperty.homMk
    ((DerivedCategory.bifunctorRHomBidual (ProEtaleWeilSheaf.bifunctorEvaluation k₀ l X)
      (ProEtaleWeilSheaf.precompQuasiIso k₀ l X (DerivedCategory.kInjectiveRep W.obj))).app K.obj)
  naturality _ _ f := ObjectProperty.hom_ext _
    ((DerivedCategory.bifunctorRHomBidual (ProEtaleWeilSheaf.bifunctorEvaluation k₀ l X)
      (ProEtaleWeilSheaf.precompQuasiIso k₀ l X
        (DerivedCategory.kInjectiveRep W.obj))).naturality f.hom)

/-- **Verdier biduality for Weil complexes** (blueprint: `theorem-verdier-biduality`): if the
underlying complex on the geometric fibre `X̄` of the Weil complex `W` is the dualizing complex
of `X̄`, the double-dual morphism `K ⟶ D_W D_W K` is an isomorphism. -/
theorem isIso_toDualDual_app
    (hW : Nonempty ((ProEtaleWeilSheaf.nativeGeometricForget k₀ l X).obj W.obj ≅
      (ObjectProperty.ι _).obj (CondensedRing.dualizingComplex l (geometricFiberOver X))))
    (K : WeilComplex k₀ l X) : IsIso ((toDualDual W).app K) := by
  let U := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
  have : U.PreservesKInjectiveComplexes := ProEtaleWeilSheaf.forgetKInjective
  let E := ProEtaleWeilSheaf.bifunctorEvaluation k₀ l X
  let I := DerivedCategory.kInjectiveRep W.obj
  let F := ProEtale.AdicSheaf.forgetAb l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ⋙
    Mod.comap (ProEtale.nativeModuleCoefficientIso l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).hom
  have : (ProEtale.constantModelBoundedConstructible (Profinite.padicAlgClRingObj l)
      (geometricFiberOver (k₀ := k₀) X).left).IsClosedUnderIsomorphisms :=
    (ProEtale.constantModelConstructibleFiniteTor_wellDefined
      (Profinite.padicAlgClRingObj l) (geometricFiberOver (k₀ := k₀) X).left).2.1
  -- reduce to the derived category, and to a complex `M` representing `K`
  suffices h : IsIso ((DerivedCategory.bifunctorRHomBidual E
      (ProEtaleWeilSheaf.precompQuasiIso k₀ l X I)).app K.obj) by
    have : IsIso ((ObjectProperty.ι (WeilComplex.objectProperty k₀ l X)).map
      ((toDualDual W).app K)) := h
    exact (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map _
  let M := DerivedCategory.Q.objPreimage K.obj
  let e : DerivedCategory.Q.obj M ≅ K.obj := DerivedCategory.Q.objObjPreimageIso K.obj
  rw [← NatTrans.isIso_app_iff_of_iso _ e,
    DerivedCategory.isIso_bifunctorRHomBidual_app_Q_obj_iff,
    ← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ U,
    ← quasiIso_iff_comp_right _ ((CochainComplex.bifunctorHomObjMapIso
      (CochainComplex.bifunctorHomObj (ProEtaleWeilSheaf.ihomBifunctor k₀ l X) M I) I
      (ProEtaleWeilSheaf.ihomBifunctorMapIso k₀ l X)).hom ≫
        CochainComplex.bifunctorHomMapLeft (CochainComplex.bifunctorHomObjMapIso M I
          (ProEtaleWeilSheaf.ihomBifunctorMapIso k₀ l X)).inv),
    CochainComplex.map_bifunctorHomBidual E M I _ _
      (ProEtaleWeilSheaf.bifunctorEvaluation_mapCompatible k₀ l X)]
  -- the underlying double-dual morphism of `ℓ`-adic sheaves
  refine ProEtaleWeilSheaf.quasiIso_bifunctorHomBidual_ordinary (geometricFiberOver X) ?_ ?_
  · obtain ⟨eW⟩ := hW
    exact ⟨F.mapDerivedCategory.mapIso ((U.mapDerivedCategoryFactors.app I).symm ≪≫
      U.mapDerivedCategory.mapIso (DerivedCategory.kInjectiveRepIso W.obj).symm) ≪≫ eW⟩
  · have hK := ((ProEtaleWeilSheaf.weil_geometric_hom_constructibility k₀ l X).1 K.obj).1
      K.property
    exact ObjectProperty.prop_of_iso _ ((ProEtaleWeilSheaf.nativeGeometricForget k₀ l X).mapIso
      e.symm ≪≫ F.mapDerivedCategory.mapIso (U.mapDerivedCategoryFactors.app M)) hK

/-- **Verdier biduality for Weil complexes** (blueprint: `theorem-verdier-biduality`), as a
natural isomorphism `𝟭 ≅ D_W D_W`. -/
theorem nonempty_iso_dual_rightOp_comp_dual
    (hW : Nonempty ((ProEtaleWeilSheaf.nativeGeometricForget k₀ l X).obj W.obj ≅
      (ObjectProperty.ι _).obj (CondensedRing.dualizingComplex l (geometricFiberOver X)))) :
    Nonempty (𝟭 (WeilComplex k₀ l X) ≅ (dual W).rightOp ⋙ dual W) :=
  have := isIso_toDualDual_app W hW
  have : IsIso (toDualDual W) := NatIso.isIso_of_isIso_app _
  ⟨asIso (toDualDual W)⟩

end WeilComplex

end AlgebraicGeometry
