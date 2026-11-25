/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricPoint
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Charts
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal

/-!
# Smooth duality for affine space from the affine line

The induction step of blueprint `lemma-affine-space-etale-localization--1`: the projection
`p_{d+1} : 𝔸^{d+1}_S ⟶ S` is, up to the isomorphism `𝔸^{d+1}_S ≅ 𝔸¹_{𝔸^d_S}`, the composite of
the affine-line projection over `𝔸^d_S` and of `p_d`. The canonical tensor maps compose
(`AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_comp_of_forall`), and the dualizing
complexes multiply, `ω_{p_{d+1}} ≅ ω_q ⊗ᴸ Lq^* ω_{p_d}`; the derived tensor product of shifted
rank-one local systems is again one, in the sum of the degrees
(`AlgebraicGeometry.Etale.IsShiftedRankOneLocalSystem.tensor`). So smooth duality for the
affine-line projections over affine bases gives smooth duality for all affine-space projections
(`AlgebraicGeometry.Etale.affineSpaceSmoothDuality_of_affineLineSmoothDuality`), in degree
`-2d`: the twists add.

## Main statements

- `AlgebraicGeometry.Etale.isLocallyConstantSheaf_tensorObj`
- `AlgebraicGeometry.Etale.IsShiftedRankOneLocalSystem.tensor`
- `AlgebraicGeometry.Etale.isShiftedRankOneLocalSystem_unit`
- `AlgebraicGeometry.Etale.affineSpaceSmoothDuality_of_affineLineSmoothDuality`
- `AlgebraicGeometry.Etale.exists_dualizingComplex_iso_and_tensor_of_etale_of_affineLine`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The tensor product of two locally constant sheaves of `Λ`-modules is locally constant: on a
common trivialising cover it is the tensor product of two constant sheaves, which is the constant
sheaf at the tensor product, pullback and the constant sheaf functor being monoidal. -/
theorem isLocallyConstantSheaf_tensorObj {X : Scheme.{u}}
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsLocallyConstantSheaf F]
    [IsLocallyConstantSheaf G] : IsLocallyConstantSheaf (F ⊗ G) := by
  obtain ⟨𝒰, h𝒰⟩ := IsLocallyConstantSheaf.exists_cover₂ F G
  have (i : 𝒰.I₀) : IsLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj (F ⊗ G)) := by
    obtain ⟨hF, hG⟩ := h𝒰 i
    obtain ⟨M, ⟨eM⟩⟩ := ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj F)
      |>.mem_essImage_of_isConstant
    obtain ⟨N, ⟨eN⟩⟩ := ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj G)
      |>.mem_essImage_of_isConstant
    refine Sheaf.IsConstant.isLocallyConstantSheaf (Sheaf.isConstant_of_iso _ (X := M ⊗ N) ?_)
    exact (Functor.Monoidal.μIso (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)) F G).symm ≪≫
      tensorIso eM.symm eN.symm ≪≫
      Functor.Monoidal.μIso (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)) M N
  exact IsLocallyConstantSheaf.of_cover 𝒰 _

/-- The stalk of a tensor product of sheaves of `Λ`-modules at a geometric point is the tensor
product of the stalks. -/
noncomputable def sheafFiberTensorObjIso {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (pointSmallEtale s).sheafFiber.obj (F ⊗ G) ≅
      (pointSmallEtale s).sheafFiber.obj F ⊗ (pointSmallEtale s).sheafFiber.obj G :=
  ((pointSmallEtale s).uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} Λ)).symm.app _ ≪≫
    sheafFiberTensorIso s F G ≪≫
    tensorIso (((pointSmallEtale s).uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} Λ)).app F)
      (((pointSmallEtale s).uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} Λ)).app G)

/-- A locally constant sheaf with free rank-one stalks is flat, having a tensor inverse. -/
lemma flat_of_isLocallyConstantSheaf {X : Scheme.{u}}
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsLocallyConstantSheaf L]
    (hL : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Nonempty ((pointSmallEtale s).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) :
    ObjectProperty.flat L :=
  ObjectProperty.flat_of_tensorIso (tensorIhomUnitIsoOfIsLocallyConstantSheaf L hL)

namespace IsShiftedRankOneLocalSystem

variable {X : Scheme.{u}}

/-- The derived tensor product of shifted rank-one local systems in degrees `-a` and `-b` is a
shifted rank-one local system in degree `-(a + b)`: `L[a] ⊗ᴸ L'[b] ≅ (L ⊗ L')[a + b]`, the
derived tensor product of the flat sheaf `L` with `L'` being the tensor product of sheaves. -/
theorem tensor
    {M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} {a b : ℤ}
    (hM : IsShiftedRankOneLocalSystem M a) (hN : IsShiftedRankOneLocalSystem N b) :
    IsShiftedRankOneLocalSystem (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj M).obj N)
      (a + b) := by
  obtain ⟨L, hL, hsL, ⟨eM⟩⟩ := hM
  obtain ⟨L', hL', hsL', ⟨eN⟩⟩ := hN
  have hflat := flat_of_isLocallyConstantSheaf L hsL
  refine ⟨L ⊗ L', isLocallyConstantSheaf_tensorObj L L', fun Ω _ _ s ↦
    ⟨sheafFiberTensorObjIso s L L' ≪≫ tensorIso (hsL Ω s).some (hsL' Ω s).some ≪≫
      λ_ (ModuleCat.of Λ Λ)⟩, ⟨?_⟩⟩
  exact ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).mapIso eM).app N ≪≫
    ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj _).mapIso eN ≪≫
    derivedTensorShiftIso _ _ _ a b ≪≫
    (shiftFunctor _ (a + b)).mapIso (singleFunctorObjTensorIso _ _ hflat)

end IsShiftedRankOneLocalSystem

/-- The unit `Λ_X` of `D(X_ét, Λ)` is a shifted rank-one local system in degree `0`: it is the
constant sheaf `Λ_X`, placed in degree zero. -/
theorem isShiftedRankOneLocalSystem_unit (X : Scheme.{u}) :
    IsShiftedRankOneLocalSystem
      (𝟙_ (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))) 0 :=
  ⟨𝟙_ _, inferInstance, fun _ _ _ s ↦
    ⟨((pointSmallEtale s).uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} Λ)).symm.app _ ≪≫
      sheafFiberUnitIso (ModuleCat.{u + 1} Λ) s⟩,
    ⟨constantComplexIsoSingleFunctor Λ X ≪≫ (shiftFunctorZero _ ℤ).symm.app _⟩⟩

variable [Finite Λ]

variable (Λ) in
/-- *Smooth duality for affine-line projections*: for every affine scheme `S` on which the
exponent of `Λ` is invertible, the projection `p : 𝔸¹_S ⟶ S` satisfies smooth duality in degree
`-2`: its dualizing complex is a locally constant sheaf of free rank-one `Λ`-modules placed in
degree `-2` and its canonical tensor maps are isomorphisms. This is what the affine-line
adjunction `Rp_! ⊣ p^*(1)[2]` (`lemma-affine-space-etale-localization--1` for `d = 1`, from
`proposition-adjunction-projective-line--1`) gives, together with its compatibility with the tensor
maps. -/
def AffineLineSmoothDuality : Prop :=
  ∀ (S : Scheme.{u}) [IsAffine S] [HasInvertibleExponent Λ S],
    SatisfiesSmoothDuality Λ (𝔸(ULift.{u} (Fin 1); S) ↘ S) 2

/-- Smooth duality for an isomorphism, in degree `0`, from smooth duality for étale morphisms. -/
theorem satisfiesSmoothDuality_of_isIso (hE : EtaleSmoothDuality Λ) {V W : Scheme.{u}}
    (e : V ⟶ W) [IsIso e] : SatisfiesSmoothDuality Λ e 0 := by
  intro _
  obtain ⟨hθ, ⟨hω⟩⟩ := hE e
  exact ⟨(isShiftedRankOneLocalSystem_unit V).of_iso hω.symm, hθ⟩

/-- **Smooth duality for affine space from the affine line** (the induction of blueprint
`lemma-affine-space-etale-localization--1`): if étale morphisms and affine-line projections over
affine bases satisfy smooth duality, then so do the projections `p_d : 𝔸^d_S ⟶ S` over affine bases
on which the exponent of `Λ` is invertible, in degree `-2d`. For `d = 0` the projection is an
isomorphism; for `d + 1` it is, through `𝔸^{d+1}_S ≅ 𝔸¹_{𝔸^d_S}`
(`AlgebraicGeometry.AffineSpace.sumIso`), the composite of the affine-line projection over
`𝔸^d_S` and of `p_d`, whose dualizing complexes multiply and whose tensor maps compose. -/
theorem affineSpaceSmoothDuality_of_affineLineSmoothDuality (hE : EtaleSmoothDuality Λ)
    (h₁ : AffineLineSmoothDuality Λ) : AffineSpaceSmoothDuality Λ := by
  intro d S _ _
  suffices h : SatisfiesSmoothDuality Λ (𝔸(ULift.{u} (Fin d); S) ↘ S) (2 * d : ℤ) by
    obtain ⟨hω, hθ⟩ := h
    exact ⟨hθ, hω⟩
  induction d with
  | zero =>
    rw [Nat.cast_zero, mul_zero]
    exact satisfiesSmoothDuality_of_isIso hE (𝔸(ULift.{u} (Fin 0); S) ↘ S)
  | succ d ih =>
    intro _
    set φ : 𝔸(ULift.{u} (Fin (d + 1)); S) ≅ 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); S)) :=
      AffineSpace.reindexIso S ((Equiv.sumCongr Equiv.ulift Equiv.ulift).trans
        (finSumFinEquiv.trans Equiv.ulift.symm)) ≪≫ AffineSpace.sumIso S
    set q := 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); S)) ↘ 𝔸(ULift.{u} (Fin d); S)
    set p := 𝔸(ULift.{u} (Fin d); S) ↘ S
    have : HasCompactification (φ.hom ≫ q) := HasCompactification.comp_of_isOpenImmersion q φ.hom
    have h : (φ.hom ≫ q) ≫ p = 𝔸(ULift.{u} (Fin (d + 1)); S) ↘ S := by
      rw [Category.assoc, Iso.trans_hom, Category.assoc, AffineSpace.sumIso_hom_over_over,
        AffineSpace.reindexIso_hom, AffineSpace.reindex_over]
    have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin d); S) := .of_hom p
    obtain ⟨hωφ, hθφ⟩ := satisfiesSmoothDuality_of_isIso hE φ.hom
    obtain ⟨hωq, hθq⟩ := h₁ 𝔸(ULift.{u} (Fin d); S)
    obtain ⟨hωp, hθp⟩ := ih
    -- the composite `a = φ ≫ q`
    have hθa (K) : IsIso (dualizingComplexTensorMap Λ (φ.hom ≫ q) K) :=
      isIso_dualizingComplexTensorMap_comp_of_forall Λ φ.hom q _ rfl hθφ hωq.isInvertible K
        (hθq K)
    have hωa : IsShiftedRankOneLocalSystem (dualizingComplex Λ (φ.hom ≫ q))
        2 := by
      obtain ⟨c⟩ := nonempty_dualizingComplex_comp_iso_of_isIso Λ φ.hom q _ rfl (hθφ _)
      have h0 := hωφ.tensor (hωq.leftDerivedUpperStar φ.hom)
      rw [zero_add] at h0
      exact h0.of_iso c.symm
    -- the composite `a ≫ p_d`
    refine ⟨?_, fun K ↦ isIso_dualizingComplexTensorMap_comp_of_forall Λ _ p _ h hθa
      hωp.isInvertible K (hθp K)⟩
    obtain ⟨c⟩ := nonempty_dualizingComplex_comp_iso_of_isIso Λ _ p _ h (hθa _)
    refine (IsShiftedRankOneLocalSystem.of_iso c.symm ?_)
    convert hωa.tensor (hωp.leftDerivedUpperStar (φ.hom ≫ q)) using 1
    push_cast
    ring

/-- **Smooth duality from the étale and affine-line cases** (the reduction in the proofs of
blueprint `proposition-exceptional-inverse-image-smooth-morphism` and
`lemma-affine-space-etale-localization--1`): if étale morphisms and the affine-line projections over
affine bases satisfy smooth duality (`AlgebraicGeometry.Etale.EtaleSmoothDuality`,
`AlgebraicGeometry.Etale.AffineLineSmoothDuality`), then for every smooth `f : X ⟶ Y` of relative
dimension `d` admitting a compactification, with the exponent of `Λ` invertible on `X`,
`ω_f ≅ L[2d]` for a locally constant sheaf `L` of free rank-one `Λ`-modules and
`θ_{f,K} : ω_f ⊗ᴸ Lf^* K ⟶ Rf^! K` is an isomorphism for every `K`; this is the statement of
`AlgebraicGeometry.Etale.exists_dualizingComplex_iso_and_tensor`. -/
theorem exists_dualizingComplex_iso_and_tensor_of_etale_of_affineLine
    (hE : EtaleSmoothDuality Λ) (h₁ : AffineLineSmoothDuality Λ) {X Y : Scheme.{u}}
    [HasInvertibleExponent Λ X] (f : X ⟶ Y) [HasCompactification f] (d : ℕ)
    [SmoothOfRelativeDimension d f] :
    ∃ L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsLocallyConstantSheaf L ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
        Nonempty ((pointSmallEtale s).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) ∧
      Nonempty (dualizingComplex Λ f ≅
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L)⟦(2 * d : ℤ)⟧) ∧
      ∀ K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        IsIso (dualizingComplexTensorMap Λ f K) :=
  exists_dualizingComplex_iso_and_tensor_of_etale_of_affineSpace hE
    (affineSpaceSmoothDuality_of_affineLineSmoothDuality hE h₁) f d

end Etale

end AlgebraicGeometry
