/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UniversalHomeomorphism
public import WeilConjectures.TraceFormula.Specialization.NearbyProperExchangeNoetherian
public import WeilConjectures.TraceFormula.Specialization.ThickOriginPowFibre
public import WeilConjectures.Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.TraceFormula.Specialization.ThickOriginReducedUnit
public import WeilConjectures.TraceFormula.Specialization.ThickOriginRestrictedUnit

/-!

# The specialization unit of the thick origin on the zero section

Let `𝒟 = 𝒟_{V(x^m)} 𝔸¹_k` be the deformation to the normal cone of the thick origin over the trait
`S = Spec k'⟦t⟧`, and `e` the zero section of its special fibre. We prove that the restriction
`Le^* σ_𝒟` of the specialization unit to the zero section is an isomorphism
(`ProEtale.CondensedRing.isIso_upperStar_zeroSection_unit_polyAffineThickOrigin`), the remaining
hypothesis of `ProEtale.CondensedRing.isZero_specializationDefect_polyAffineThickOrigin_unit`.

The power map `ν : 𝒲 ⟶ 𝒟` from the deformation `𝒲 = 𝒟_{V(x)} 𝔸¹_k ≅ 𝔸¹ × S` of the origin, over
`t ↦ t^m` (`ProEtale.CondensedRing.powModelHom`), is finite and an isomorphism on geometric generic
fibres. Its source has invertible specialization unit (smooth exchange,
`isIso_deformationModel_polyAffineThickOrigin_one_unit`, and topological invariance along the
thickening `t = 0 ⊆ t^m = 0`). The proper exchange `Ψ_𝒟 ≅ Rν_{s*} Ψ_𝒲` and its unit identity
then identify `σ_𝒟` with the unit `Λ ⟶ Rν_{s*} Lν_s^* Λ`, whose restriction to a rational point of
the zero section is invertible by proper base change, the fibre of `ν_s` over that point being a
universally homeomorphic point
(`ProEtale.CondensedRing.mem_range_zeroSectionSpecialFibreMap_of_powMap`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Point

variable {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k']

instance : IsIso (deformationSpecialFibre (point k) ⊥ k').hom := by
  have : IsIso (point k).hom := inferInstanceAs (IsIso (𝟙 _))
  exact inferInstanceAs (IsIso (pullback.snd _ _))

/-- The rational point of the special fibre of the constant family `Y × S` lying over a rational
point `y` of `Y`. -/
noncomputable def constantFamilySpecialPoint {Y : Over (Spec (.of k))} (y : point k ⟶ Y) :
    Spec (.of k') ⟶ (deformationSpecialFibre Y ⊥ k').left :=
  inv (deformationSpecialFibre (point k) ⊥ k').hom ≫
    (deformationSpecialFibreMap y (siteIdeal_bot_map_appLE_le _ ⊥) k').left

@[reassoc (attr := simp)]
lemma constantFamilySpecialPoint_hom {Y : Over (Spec (.of k))} (y : point k ⟶ Y) :
    constantFamilySpecialPoint k' y ≫ (deformationSpecialFibre Y ⊥ k').hom = 𝟙 _ := by
  rw [constantFamilySpecialPoint, Category.assoc, Over.w, IsIso.inv_hom_id]

end Point

section PowModel

variable (k : Type u) [Field k] (k' : Type u) [Field k'] [Algebra k k'] {m : ℕ} (hm : m ≠ 0)

variable (m) in
/-- The power map `D_{V(x)} 𝔸¹_k ⟶ D_{V(x^m)} 𝔸¹_k` of deformation spaces. -/
noncomputable abbrev thickOriginPowMap :
    (polyAffineThickOrigin k 1).deformationSpace ⟶ (polyAffineThickOrigin k m).deformationSpace :=
  IdealSheafData.deformationSpacePowMap m fun U ↦ (siteIdeal_polyAffineThickOrigin k m U).le

/-- The power model `𝒲` of the thick origin: the deformation of `V(x)` with the thickened special
fibre `t^m = 0`. -/
noncomputable abbrev thickOriginPowSourceModel :=
  powSourceModel k' hm (polyAffine k 1) (polyAffineThickOrigin k 1) (polyAffineThickOrigin k m)
    (thickOriginPowMap k m) (affineLinePowMap k m)
    (deformationSpacePowMap_deformationSpaceToAffineLine _) (traitPowMap_traitToAffineLine k k' hm)

/-- The special fibre of the power model, over `k'`. -/
noncomputable abbrev thickOriginPowSpecialFibre :=
  powSpecialFibre k' hm (polyAffine k 1) (polyAffineThickOrigin k 1) (polyAffineThickOrigin k m)
    (thickOriginPowMap k m) (affineLinePowMap k m)
    (deformationSpacePowMap_deformationSpaceToAffineLine _) (traitPowMap_traitToAffineLine k k' hm)

/-- The morphism of special fibres `ν_s : 𝒲_s ⟶ 𝒟_s` of the power model. -/
noncomputable abbrev thickOriginPowSpecialFibreMap :
    thickOriginPowSpecialFibre k k' hm ⟶
      deformationSpecialFibre (polyAffine k 1) (polyAffineThickOrigin k m) k' :=
  powSpecialFibreMap k' hm (polyAffine k 1) (polyAffineThickOrigin k 1)
    (polyAffineThickOrigin k m) (thickOriginPowMap k m) (affineLinePowMap k m)
    (deformationSpacePowMap_deformationSpaceToAffineLine _) (traitPowMap_traitToAffineLine k k' hm)

/-- The morphism of models `𝒲 ⟶ 𝒟_{V(x^m)}` over the identity of `𝔸¹_k`. -/
noncomputable abbrev thickOriginPowModelHom :=
  powModelHom k' hm (polyAffine k 1) (polyAffineThickOrigin k 1) (polyAffineThickOrigin k m)
    (thickOriginPowMap k m) (affineLinePowMap k m)
    (deformationSpacePowMap_deformationSpaceToAffineLine _) (traitPowMap_traitToAffineLine k k' hm)
    (IdealSheafData.deformationSpacePowMap_proj _)

/-- The inclusion `c : 𝒟_{V(x),s} ⟶ 𝒲_s` of the special fibre into the thickened one. -/
noncomputable abbrev thickOriginSpecialFibreToPow :
    (deformationSpecialFibre (polyAffine k 1) (polyAffineThickOrigin k 1) k').left ⟶
      (thickOriginPowSpecialFibre k k' hm).left :=
  specialFibreToPowSpecialFibre k' hm (polyAffine k 1) (polyAffineThickOrigin k 1)
    (polyAffineThickOrigin k m) (thickOriginPowMap k m) (affineLinePowMap k m)
    (deformationSpacePowMap_deformationSpaceToAffineLine _) (traitPowMap_traitToAffineLine k k' hm)

/-- The morphism of models `𝒟_{V(x)} ⟶ 𝒲` given by the identity of the total space and the
inclusion `c` of the special fibres. -/
noncomputable def thickOriginToPowSourceModel :
    (deformationModel (polyAffine k 1) (polyAffineThickOrigin k 1) k').Hom
      (thickOriginPowSourceModel k k' hm) (𝟙 _) (thickOriginSpecialFibreToPow k k' hm) where
  total := 𝟙 _
  generic := 𝟙 _
  comm_j := by rw [Category.id_comp, Category.comp_id]; rfl
  comm_i := by rw [Category.comp_id, specialFibreToPowSpecialFibre_i]
  comm_ε := by rw [Category.id_comp, Category.comp_id]; rfl

end PowModel

section GenericUnit

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- If a morphism of models `M ⟶ N` over the identity of `X` has invertible morphisms of total
spaces and of geometric generic fibres, and its morphism of special fibres is a universal
homeomorphism, the specialization unit of `N` is invertible as soon as that of `M` is. -/
theorem NearbyCyclesModel.isIso_unit_of_hom {X X' Y' : Scheme.{u}} {M : NearbyCyclesModel X X'}
    {N : NearbyCyclesModel X Y'} {c : X' ⟶ Y'} (ψ : M.Hom N (𝟙 X) c) [IsIso ψ.total]
    [IsIso ψ.generic] [IsUniversalHomeomorphism c] (hM : IsIso (M.unit Λ)) :
    IsIso (N.unit Λ) := by
  have := ψ.isIso_pullbackExchange_of_isIso Λ
  have h := ψ.map_unit_comp_pullbackExchange_app Λ
  have : IsIso (L((c)^*⟦Λ⟧).map (N.unit Λ) ≫ (ψ.pullbackExchange Λ).app (𝟙_ _)) := by
    rw [h]; infer_instance
  exact isIso_of_isIso_leftDerivedUpperStar_map Λ c _
    (IsIso.of_isIso_comp_right (L((c)^*⟦Λ⟧).map (N.unit Λ)) ((ψ.pullbackExchange Λ).app (𝟙_ _)))

/-- The unit of `L(𝟙)^* ⊣ R(𝟙)_*` is an isomorphism. -/
lemma isIso_derivedUpperStarLowerStarAdjunction_id_unit (X : Scheme.{u}) :
    IsIso (derivedUpperStarLowerStarAdjunction Λ (𝟙 X)).unit := by
  have : (L((𝟙 X)^*⟦Λ⟧)).Full := Functor.Full.of_iso (leftDerivedUpperStarId Λ X).symm
  have : (L((𝟙 X)^*⟦Λ⟧)).Faithful := Functor.Faithful.of_iso (leftDerivedUpperStarId Λ X).symm
  exact (derivedUpperStarLowerStarAdjunction Λ (𝟙 X)).unit_isIso_of_L_fully_faithful

/-- **Restricted specialization unit from the proper exchange**: let `φ : M ⟶ N` be a morphism of
models over the identity of `X`, with morphism `f'` of special fibres, whose pushforward exchange
is invertible at the unit and such that the specialization unit of `M` is invertible. If the unit
`Λ ⟶ Rf'_* Lf'^* Λ` becomes invertible after `Le^*`, so does the specialization unit of `N`.
Indeed, by the unit identity of the pushforward exchange the square
```
Λ --------σ_N--------> Ψ_N Λ --Ψ_N(η)--> Ψ_N R𝟙_* Λ --χ--> Rf'_* Ψ_M Λ
|η_{f'}                                                       ‖
v                                                             ‖
Rf'_* Lf'^* Λ ------------Rf'_*(Ψ_M(ε) ∘ σ_M ∘ ε⁻¹)------> Rf'_* Ψ_M Λ
```
commutes, and all its morphisms except `σ_N` are invertible after `Le^*`. -/
theorem NearbyCyclesModel.isIso_upperStar_unit_of_pushforwardExchange {X X' Y' T : Scheme.{u}}
    {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel X Y'} {f' : X' ⟶ Y'}
    (φ : M.Hom N (𝟙 X) f')
    (hχ : IsIso ((φ.pushforwardExchange Λ).app (L((𝟙 X)^*⟦Λ⟧).obj (𝟙_ _))))
    (hM : IsIso (M.unit Λ)) (e : T ⟶ Y')
    (he : IsIso (L((e)^*⟦Λ⟧).map ((derivedUpperStarLowerStarAdjunction Λ f').unit.app (𝟙_ _)))) :
    IsIso (L((e)^*⟦Λ⟧).map (N.unit Λ)) := by
  have := isIso_derivedUpperStarLowerStarAdjunction_id_unit Λ X
  exact isIso_map_of_map_comp_eq L((e)^*⟦Λ⟧)
    (φ.unit_comp_map_unit_comp_pushforwardExchange_app Λ) hχ he

/-- Restriction along `r ≫ e` with `r` a universal homeomorphism detects isomorphisms after
restriction along `e`: in the commutative square
```
L(r ≫ e)^* K --L(r ≫ e)^* g--> L(r ≫ e)^* L
|≅                              |≅
v                               v
Lr^* Le^* K ---Lr^* Le^* g----> Lr^* Le^* L
```
the top map is invertible, hence so is the bottom one, and `Lr^*` reflects isomorphisms. -/
lemma isIso_leftDerivedUpperStar_map_of_comp {A B C : Scheme.{u}} (r : A ⟶ B) (e : B ⟶ C)
    [IsUniversalHomeomorphism r]
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology C) Ab.{u + 1}) (condensedRingObj Λ C))}
    (g : K ⟶ L) (h : IsIso (L((r ≫ e)^*⟦Λ⟧).map g)) : IsIso (L((e)^*⟦Λ⟧).map g) := by
  refine isIso_of_isIso_leftDerivedUpperStar_map Λ r _ ?_
  have hn := (leftDerivedUpperStarComp Λ r e).hom.naturality g
  have : IsIso ((leftDerivedUpperStarComp Λ r e).hom.app K ≫
      L((r)^*⟦Λ⟧).map (L((e)^*⟦Λ⟧).map g)) := by
    erw [← hn]; infer_instance
  exact IsIso.of_isIso_comp_left ((leftDerivedUpperStarComp Λ r e).hom.app K) _

end GenericUnit

section Unit

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] {m : ℕ} (hm : m ≠ 0)

/-- The specialization unit of the power model `𝒲` is an isomorphism: its restriction along the
universal homeomorphism `c` is the specialization unit of the deformation of the origin. -/
theorem isIso_thickOriginPowSourceModel_unit :
    IsIso ((thickOriginPowSourceModel k k' hm).unit (Profinite.padicAlgClRingObj ℓ)) := by
  have : IsIso ((thickOriginToPowSourceModel k k' hm).total) := inferInstanceAs (IsIso (𝟙 _))
  have : IsIso ((thickOriginToPowSourceModel k k' hm).generic) := inferInstanceAs (IsIso (𝟙 _))
  exact NearbyCyclesModel.isIso_unit_of_hom _ (thickOriginToPowSourceModel k k' hm)
    (isIso_deformationModel_polyAffineThickOrigin_one_unit k')

end Unit

section Geometry

variable (k : Type u) [Field k] (k' : Type u) [Field k'] [Algebra k k'] {m : ℕ} (hm : m ≠ 0)

/-- The origin, as a rational point of the centre `V(x^m)`. -/
noncomputable abbrev thickOriginRationalPoint (m : ℕ) (hm : 0 < m) :
    point k ⟶ centre (polyAffine k 1) (polyAffineThickOrigin k m) :=
  Over.homMk (thickOriginPoint k hm) (thickOriginPoint_hom k hm)

/-- The rational point of the zero section of the special fibre of `𝒟_{V(x^m)}`. -/
noncomputable abbrev thickOriginZeroSectionPoint (m : ℕ) (hm : 0 < m) :
    Spec (.of k') ⟶
      (deformationSpecialFibre (centre (polyAffine k 1) (polyAffineThickOrigin k m)) ⊥ k').left :=
  constantFamilySpecialPoint k' (thickOriginRationalPoint k m hm)

instance (m : ℕ) [NeZero m] :
    IsUniversalHomeomorphism
      (deformationSpecialFibre (centre (polyAffine k 1) (polyAffineThickOrigin k m)) ⊥ k').hom := by
  have := isUniversalHomeomorphism_centre_polyAffineThickOrigin k
    (Nat.pos_of_ne_zero (NeZero.ne m))
  exact inferInstanceAs (IsUniversalHomeomorphism (pullback.snd _ _))

instance (m : ℕ) [NeZero m] :
    Subsingleton
      (deformationSpecialFibre (centre (polyAffine k 1) (polyAffineThickOrigin k m)) ⊥ k').left :=
  ⟨fun _ _ ↦ (deformationSpecialFibre (centre (polyAffine k 1)
    (polyAffineThickOrigin k m)) ⊥ k').hom.isHomeomorph.injective (Subsingleton.elim _ _)⟩

/-- The rational point `w = c(e(0))` of the thickened special fibre of the power model. -/
noncomputable abbrev thickOriginPowPoint :
    Spec (.of k') ⟶ (thickOriginPowSpecialFibre k k' hm).left :=
  thickOriginZeroSectionPoint k k' 1 one_pos ≫
    (zeroSectionSpecialFibreMap (polyAffine k 1) (polyAffineThickOrigin k 1) k').left ≫
      thickOriginSpecialFibreToPow k k' hm

/-- Its image `o = ν_s(w)` in the special fibre of `𝒟_{V(x^m)}`. -/
noncomputable abbrev thickOriginPowImagePoint :
    Spec (.of k') ⟶
      (deformationSpecialFibre (polyAffine k 1) (polyAffineThickOrigin k m) k').left :=
  thickOriginPowPoint k k' hm ≫ (thickOriginPowSpecialFibreMap k k' hm).left

lemma thickOriginSpecialFibreToPow_powSpecialFibreMap :
    thickOriginSpecialFibreToPow k k' hm ≫ (thickOriginPowSpecialFibreMap k k' hm).left =
      deformationSpecialFibrePowMap k' hm (polyAffine k 1) (polyAffineThickOrigin k 1)
        (polyAffineThickOrigin k m) (thickOriginPowMap k m) (affineLinePowMap k m)
        (deformationSpacePowMap_deformationSpaceToAffineLine _)
        (traitPowMap_traitToAffineLine k k' hm) :=
  pullback.lift_fst _ _ _

lemma thickOriginPowImagePoint_hom :
    thickOriginPowImagePoint k k' hm ≫
      (deformationSpecialFibre (polyAffine k 1) (polyAffineThickOrigin k m) k').hom = 𝟙 _ := by
  simp only [thickOriginPowImagePoint, thickOriginPowPoint, Category.assoc]
  rw [reassoc_of% thickOriginSpecialFibreToPow_powSpecialFibreMap, deformationSpecialFibrePowMap]
  erw [pullback.lift_snd]
  rw [Over.w, constantFamilySpecialPoint_hom]

/-- The image point `o` lies on the zero section: it is the zero-section point of `V(x^m)`. -/
lemma thickOriginPowImagePoint_eq :
    thickOriginPowImagePoint k k' hm = thickOriginZeroSectionPoint k k' m
      (Nat.pos_of_ne_zero hm) ≫
        (zeroSectionSpecialFibreMap (polyAffine k 1) (polyAffineThickOrigin k m) k').left := by
  have : NeZero m := ⟨hm⟩
  refine Scheme.ext_of_comp_eq_id_of_apply_eq
    (deformationSpecialFibre (polyAffine k 1) (polyAffineThickOrigin k m) k').hom
    (thickOriginPowImagePoint_hom k k' hm) (by rw [Category.assoc, Over.w,
      constantFamilySpecialPoint_hom]) ?_
  obtain ⟨ζ, hζ⟩ := deformationSpecialFibrePowMap_mem_range_zeroSectionSpecialFibreMap k' hm
    (polyAffine k 1) (fun U ↦ (siteIdeal_polyAffineThickOrigin k m U).le)
    (traitPowMap_traitToAffineLine k k' hm) (Nat.pos_of_ne_zero hm)
    (thickOriginZeroSectionPoint k k' 1 one_pos (IsLocalRing.closedPoint k'))
  have hr : thickOriginZeroSectionPoint k k' m (Nat.pos_of_ne_zero hm)
      (IsLocalRing.closedPoint k') = ζ := Subsingleton.elim _ _
  have hc (x) :
      (thickOriginPowSpecialFibreMap k k' hm).left (thickOriginSpecialFibreToPow k k' hm x) =
      deformationSpecialFibrePowMap k' hm (polyAffine k 1) (polyAffineThickOrigin k 1)
        (polyAffineThickOrigin k m) (thickOriginPowMap k m) (affineLinePowMap k m)
        (deformationSpacePowMap_deformationSpaceToAffineLine _)
        (traitPowMap_traitToAffineLine k k' hm) x := by
    rw [← Scheme.Hom.comp_apply, thickOriginSpecialFibreToPow_powSpecialFibreMap]
  simp only [thickOriginPowImagePoint, thickOriginPowPoint, Scheme.Hom.comp_apply]
  rw [hc, hr, hζ]

/-- The point `o`, as a morphism of `k'`-schemes. -/
noncomputable abbrev thickOriginPowImageOver :
    point k' ⟶ deformationSpecialFibre (polyAffine k 1) (polyAffineThickOrigin k m) k' :=
  Over.homMk (thickOriginPowImagePoint k k' hm) (thickOriginPowImagePoint_hom k k' hm)

instance : IsSeparated (affineLinePowMap k m) := by
  unfold affineLinePowMap AffineSpace.linePowMap
  infer_instance

instance isFinite_thickOriginPowModelHom_total :
    IsFinite (thickOriginPowModelHom k k' hm).total := by
  have : IsFinite (thickOriginPowMap k m) := by
    have : NeZero m := ⟨hm⟩
    exact isFinite_deformationSpacePowMap_polyAffineThickOrigin k (Nat.pos_of_ne_zero hm)
  exact isFinite_deformationTotalPowMap k' hm (polyAffine k 1) (polyAffineThickOrigin k 1)
    (polyAffineThickOrigin k m) (thickOriginPowMap k m) (affineLinePowMap k m)
    (deformationSpacePowMap_deformationSpaceToAffineLine _) (traitPowMap_traitToAffineLine k k' hm)

instance : IsFinite (thickOriginPowSpecialFibreMap k k' hm).left := by
  have := isFinite_thickOriginPowModelHom_total k k' hm
  exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip this

instance : LocallyOfFiniteType (thickOriginPowSpecialFibre k k' hm).hom :=
  inferInstanceAs (LocallyOfFiniteType ((thickOriginPowSpecialFibreMap k k' hm).left ≫ _))

instance : QuasiCompact (thickOriginPowSpecialFibre k k' hm).hom :=
  inferInstanceAs (QuasiCompact ((thickOriginPowSpecialFibreMap k k' hm).left ≫ _))

instance : IsSeparated (thickOriginPowSpecialFibre k k' hm).hom :=
  inferInstanceAs (IsSeparated ((thickOriginPowSpecialFibreMap k k' hm).left ≫ _))

/-- The fibre `F = 𝒲_s ×_{𝒟_s} Spec k'` of the power map over the point `o`. -/
noncomputable abbrev thickOriginPowFibre : Over (Spec (.of k')) :=
  pullback (thickOriginPowSpecialFibreMap k k' hm) (thickOriginPowImageOver k k' hm)

lemma isPullback_thickOriginPowFibre_left :
    IsPullback (pullback.fst (thickOriginPowSpecialFibreMap k k' hm)
        (thickOriginPowImageOver k k' hm)).left
      (pullback.snd (thickOriginPowSpecialFibreMap k k' hm) (thickOriginPowImageOver k k' hm)).left
      (thickOriginPowSpecialFibreMap k k' hm).left (thickOriginPowImagePoint k k' hm) :=
  (IsPullback.of_hasPullback _ _).map (Over.forget _)

instance : IsFinite (pullback.snd (thickOriginPowSpecialFibreMap k k' hm)
    (thickOriginPowImageOver k k' hm)).left :=
  MorphismProperty.of_isPullback (isPullback_thickOriginPowFibre_left k k' hm) inferInstance

instance : IsClosedImmersion (thickOriginPowImagePoint k k' hm) :=
  isClosedImmersion_of_comp_eq_id _ _ (thickOriginPowImagePoint_hom k k' hm)

instance : IsClosedImmersion (pullback.fst (thickOriginPowSpecialFibreMap k k' hm)
    (thickOriginPowImageOver k k' hm)).left :=
  MorphismProperty.of_isPullback (isPullback_thickOriginPowFibre_left k k' hm).flip inferInstance

instance : LocallyOfFiniteType (thickOriginPowFibre k k' hm).hom := by
  rw [← Over.w (pullback.snd (thickOriginPowSpecialFibreMap k k' hm)
    (thickOriginPowImageOver k k' hm))]
  infer_instance

instance : QuasiCompact (thickOriginPowFibre k k' hm).hom := by
  rw [← Over.w (pullback.snd (thickOriginPowSpecialFibreMap k k' hm)
    (thickOriginPowImageOver k k' hm))]
  infer_instance

instance : IsSeparated (thickOriginPowFibre k k' hm).hom := by
  rw [← Over.w (pullback.snd (thickOriginPowSpecialFibreMap k k' hm)
    (thickOriginPowImageOver k k' hm))]
  infer_instance

/-- The fibre `F` is a single point: a point of `𝒲_s` over `o` comes from a point of the special
fibre of `𝒟_{V(x)}` over the zero section of `𝒟_{V(x^m)}`, hence from the zero section of
`𝒟_{V(x)}`, which is a single point. -/
instance : Subsingleton (thickOriginPowFibre k k' hm).left := by
  have : NeZero m := ⟨hm⟩
  set ν := (thickOriginPowSpecialFibreMap k k' hm).left
  set e' := (pullback.fst (thickOriginPowSpecialFibreMap k k' hm)
    (thickOriginPowImageOver k k' hm)).left
  set q := (pullback.snd (thickOriginPowSpecialFibreMap k k' hm)
    (thickOriginPowImageOver k k' hm)).left
  have key (f : (thickOriginPowFibre k k' hm).left) :
      e' f = thickOriginPowPoint k k' hm (IsLocalRing.closedPoint k') := by
    obtain ⟨y, hy⟩ := (thickOriginSpecialFibreToPow k k' hm).surjective (e' f)
    have h₁ : ν (e' f) = thickOriginPowImagePoint k k' hm (q f) := by
      rw [← Scheme.Hom.comp_apply, (isPullback_thickOriginPowFibre_left k k' hm).w,
        Scheme.Hom.comp_apply]
      rfl
    have h₂ : ν (thickOriginSpecialFibreToPow k k' hm y) =
        deformationSpecialFibrePowMap k' hm (polyAffine k 1) (polyAffineThickOrigin k 1)
          (polyAffineThickOrigin k m) (thickOriginPowMap k m) (affineLinePowMap k m)
          (deformationSpacePowMap_deformationSpaceToAffineLine _)
          (traitPowMap_traitToAffineLine k k' hm) y := by
      rw [← Scheme.Hom.comp_apply, thickOriginSpecialFibreToPow_powSpecialFibreMap]
    have hmem := mem_range_zeroSectionSpecialFibreMap_of_powMap k' hm (polyAffine k 1)
      (fun U ↦ (siteIdeal_polyAffineThickOrigin k m U).le)
      (fun U ↦ (siteIdeal_polyAffineThickOrigin k m U).ge)
      (traitPowMap_traitToAffineLine k k' hm) y (by
        rw [← h₂, hy, h₁, thickOriginPowImagePoint_eq, Scheme.Hom.comp_apply]
        exact ⟨_, rfl⟩)
    obtain ⟨z, rfl⟩ := hmem
    rw [← hy, thickOriginPowPoint, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
      Subsingleton.elim (thickOriginZeroSectionPoint k k' 1 one_pos _) z]
  refine ⟨fun a b ↦ e'.isClosedEmbedding.injective ?_⟩
  rw [key, key]

/-- The section `Spec k' ⟶ F` given by the point `w`. -/
noncomputable abbrev thickOriginPowFibreSection : point k' ⟶ thickOriginPowFibre k k' hm :=
  pullback.lift (Over.homMk (thickOriginPowPoint k k' hm) (by
      refine Eq.trans ?_ (thickOriginPowImagePoint_hom k k' hm)
      simp only [thickOriginPowImagePoint, Category.assoc]
      rfl)) (𝟙 _) (by ext; simp [thickOriginPowImagePoint])

instance : IsUniversalHomeomorphism (pullback.snd (thickOriginPowSpecialFibreMap k k' hm)
    (thickOriginPowImageOver k k' hm)).left := by
  have hs : (thickOriginPowFibreSection k k' hm).left ≫ (pullback.snd
      (thickOriginPowSpecialFibreMap k k' hm) (thickOriginPowImageOver k k' hm)).left = 𝟙 _ := by
    rw [← Over.comp_left, thickOriginPowFibreSection, pullback.lift_snd]
    rfl
  have : Subsingleton (point k').left := inferInstanceAs (Subsingleton (Spec (.of k')))
  have : IsClosedImmersion (thickOriginPowFibreSection k k' hm).left :=
    isClosedImmersion_of_comp_eq_id _ _ hs
  have : Surjective (thickOriginPowFibreSection k k' hm).left :=
    ⟨fun _ ↦ ⟨IsLocalRing.closedPoint k',
      Subsingleton.elim (α := (thickOriginPowFibre k k' hm).left) _ _⟩⟩
  exact IsUniversalHomeomorphism.of_comp_eq_id hs

end Geometry

section Main

variable {ℓ : ℕ} [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] {m : ℕ}

/-- **The specialization unit of the thick origin on the zero section**: for the deformation `𝒟`
of `V(x^m) ⊆ 𝔸¹_k` over `Spec k'⟦t⟧`, the restriction `Le^* σ_𝒟` of the specialization unit to
the zero section is an isomorphism. -/
theorem isIso_upperStar_zeroSection_unit_polyAffineThickOrigin (hm : m ≠ 0) :
    IsIso (L(((zeroSectionSpecialFibreMap (polyAffine k 1) (polyAffineThickOrigin k m)
      k').left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map ((deformationModel (polyAffine k 1)
        (polyAffineThickOrigin k m) k').unit (Profinite.padicAlgClRingObj ℓ))) := by
  have : NeZero m := ⟨hm⟩
  have hK : boundedConstructible _
      (L((𝟙 (polyAffine k 1).left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj (𝟙_ _)) :=
    (boundedConstructible _).prop_of_iso
      (leftDerivedUpperStarUnitIso _ (𝟙 (polyAffine k 1).left)).symm
      (boundedConstructible _).prop_unit
  have hD := isTraitModel_deformationModel (polyAffine k 1) (polyAffineThickOrigin k 1) k'
  have : IsNoetherian (polyAffine k 1).left :=
    isNoetherian_of_locallyOfFiniteType (polyAffine k 1).hom
  have : IsNoetherian (thickOriginPowSourceModel k k' hm).generic := hD.isNoetherian_generic
  have : IsNoetherian (thickOriginPowSourceModel k k' hm).total := hD.isNoetherian_total
  have : IsAffineHom (thickOriginPowSourceModel k k' hm).j := hD.isAffineHom_j
  have : IsClosedImmersion (deformationModel (polyAffine k 1) (polyAffineThickOrigin k m) k').i :=
    (isTraitModel_deformationModel _ _ k').isClosedImmersion_i
  have : IsClosedImmersion (thickOriginPowSourceModel k k' hm).i :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have hχ :=
    (thickOriginPowModelHom k k' hm).isIso_pushforwardExchange_app_of_isProper_of_isNoetherian
    (polyAffine k 1).hom (isTraitModel_deformationModel _ _ k').exists_over
    (isPullback_powModelHom_i k' hm _ _ _ _ _ _ _)
    (isPullback_powModelHom_ε k' hm _ _ _ _ _ _ _ (IdealSheafData.deformationSpacePowMap_proj _))
    hK
  have he := isIso_leftDerivedUpperStar_map_unit_app_unit_of_isPullback ℓ
    (IsPullback.of_hasPullback (thickOriginPowSpecialFibreMap k k' hm)
      (thickOriginPowImageOver k k' hm))
  have hM := isIso_thickOriginPowSourceModel_unit (ℓ := ℓ) (k := k) k' hm
  have ho := NearbyCyclesModel.isIso_upperStar_unit_of_pushforwardExchange _
    (thickOriginPowModelHom k k' hm) hχ hM (thickOriginPowImagePoint k k' hm) he
  rw [thickOriginPowImagePoint_eq] at ho
  have : IsUniversalHomeomorphism (thickOriginZeroSectionPoint k k' m (Nat.pos_of_ne_zero hm) ≫
      (deformationSpecialFibre (centre (polyAffine k 1) (polyAffineThickOrigin k m)) ⊥
        k').hom) := by
    rw [constantFamilySpecialPoint_hom]; infer_instance
  have : IsUniversalHomeomorphism (thickOriginZeroSectionPoint k k' m (Nat.pos_of_ne_zero hm)) :=
    IsUniversalHomeomorphism.of_comp _
      (deformationSpecialFibre (centre (polyAffine k 1) (polyAffineThickOrigin k m)) ⊥ k').hom
  exact isIso_leftDerivedUpperStar_map_of_comp _ _ _ _ ho

end Main

end AlgebraicGeometry.ProEtale.CondensedRing
