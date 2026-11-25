/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedUpperShriekFieldExtension
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingClosedImmersionLaw
public import WeilConjectures.SixFunctors.NearbyCycles.HomComp
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste
import WeilConjectures.Tactic.ExactModProofs

/-!

# Dualizing complexes, exceptional inverse images and change of the base field

Let `F` and `L` be fields and `f : Z ⟶ P` a proper morphism of `F`-schemes of finite type with a
cartesian square
```
Z' --πZ--> Z
 |f'       |f
 v         v
P' --πP--> P
```
over `πₛ : Spec L ⟶ Spec F`. This file constructs the **base change map of the exceptional inverse
image** `γ : πZ^* Rf^! ⟶ Rf'^! πP^*` on bounded constructible `ℚ̄_ℓ`-complexes
(`ProEtale.CondensedRing.upperShriekBaseChangeOfMap`): the mate, under `Rf_* ⊣ Rf^!` and
`Rf'_* ⊣ Rf'^!`, of the inverse of the proper base change isomorphism `πP^* Rf_* ≅ Rf'_* πZ^*`.

## Main results

- `ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_fieldExtension`: `γ` is an
  isomorphism for a closed immersion `f` and a field extension `L/F`.
- `ProEtale.CondensedRing.dualizingComplexBaseChange_eq_comp_upperShriekBaseChangeOfMap`: for a
  proper morphism `f : Z ⟶ X` of proper `F`-schemes, the comparison of the dualizing complexes of
  `Z` (`ProEtale.CondensedRing.dualizingComplexBaseChange`) is
  `πZ^* ω_Z ≅ πZ^* Rf^! ω_X ⟶[γ] Rf'^! πX^* ω_X ⟶[Rf'^! φ_X] Rf'^! ω_{X'} ≅ ω_{Z'}`.
- `ProEtale.CondensedRing.isIso_dualizingComplexBaseChange_iff_of_isClosedImmersion`: for a
  closed immersion `i : Z ⟶ X` of proper `F`-schemes and a field extension `L/F`, `φ_Z` is an
  isomorphism if and only if `Ri'^!(φ_X)` is; in particular `φ_Z` is an isomorphism if `φ_X` is
  (`ProEtale.CondensedRing.isIso_dualizingComplexBaseChange_of_isClosedImmersion`).

## Proofs

*Closed immersions.* As in
`ProEtale.CondensedRing.nonempty_iso_upperShriek_closedImmersion_of_fieldExtension`, complete the
unit `M ⟶ Rj_* j^* M` (`j` the open complement of `i`) to a distinguished triangle
`X ⟶ M ⟶ Rj_* j^* M ⟶`; by
`CategoryTheory.Pretriangulated.isIso_of_adjunction_triangle_of_fullyFaithful`
its first map is the counit `Ri_* Ri^! M ⟶ M` up to isomorphism. By the counit property of mates,
the transpose of `γ(M)` under `Ri'_* ⊣ Ri'^!` is `πP^*` of this counit read through proper base
change, i.e. the first map of the pulled back triangle, whose third term
`πP^* Rj_* j^* M ≅ Rj'_* πU^* j^* M` receives no maps from `Ri'_*`: the same lemma shows that `γ(M)`
is invertible (`CategoryTheory.Pretriangulated.isIso_mateEquiv_inv_app_of_triangle`).

*Composition with the comparison of dualizing complexes.* By uniqueness
(`ProEtale.CondensedRing.eq_dualizingComplexBaseChange_of_trace`) it suffices to compute the
trace of the right side. This uses the composition of traces
(`ProEtale.CondensedRing.lowerStar_map_upperShriekDualizingComplexIso_hom_comp_trace`), the counit
property of `γ`, the trace compatibility of `φ_X` and the vertical pasting of the proper base
change maps of the squares `Z' ⟶ X'` and `X' ⟶ Spec L`
(`ProEtale.CondensedRing.boundedConstructibleBaseChangeOfMap_app_comp_lowerStarCompOfEq_inv_app`,
from `ProEtale.CondensedRing.mateEquiv_comp_aux`). The diagram chase is carried out in abstract
categories (`CategoryTheory.Adjunction.app_comp_map_comp_trace_of_paste`).

## Implementation notes

As explained in `TraceFormula.Specialization.NearbyDualizingClosedImmersionLaw`, identifying
concrete terms of bounded constructible complexes whose auxiliary proofs differ can make the kernel
time out; the pasting law is therefore proved for arbitrary ambient transformations and
instantiated once, and the composition of traces is transported with `exact_mod_proofs`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Pretriangulated

variable {C D C' D' T T' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  [Category* T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]
  [Category* T'] [Preadditive T'] [HasZeroObject T'] [HasShift T' ℤ]
  [∀ n : ℤ, (shiftFunctor T' n).Additive] [Pretriangulated T']

/-- The first term of a distinguished triangle on the unit of an adjunction vanishes after
applying the left adjoint, if the counit at the pulled-back object is invertible. -/
lemma isZero_map_obj_of_distinguished_unit_triangle {F : T ⥤ T'} {G : T' ⥤ T}
    [F.CommShift ℤ] [F.IsTriangulated] (adj : F ⊣ G) {X M : T} (f : X ⟶ M)
    (h : G.obj (F.obj M) ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f (adj.unit.app M) h ∈ distTriang T)
    [IsIso (adj.counit.app (F.obj M))] : IsZero (F.obj X) := by
  refine Triangle.isZero₁_of_isIso₂ _ (F.map_distinguished _ hT) ?_
  exact IsIso.of_isIso_fac_right (hh := IsIso.id _) (adj.left_triangle_components M)

/-- In the situation of
`CategoryTheory.Pretriangulated.isIso_of_adjunction_triangle_of_fullyFaithful`,
the counit `ι (L (R B)) ⟶ ι B` is the first map of the triangle, up to isomorphism. -/
lemma exists_iso_counit_comp_eq_mor₁ {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {ι : D ⥤ T}
    (hι : ι.FullyFaithful) (hL : (L ⋙ ι).FullyFaithful) (Tr : Triangle T)
    (hT : Tr ∈ distTriang T) {P : C} {B : D} (e₁ : ι.obj (L.obj P) ≅ Tr.obj₁)
    (e₂ : ι.obj B ≅ Tr.obj₂) (h₀ : ∀ Q, Subsingleton (ι.obj (L.obj Q) ⟶ Tr.obj₃))
    (h₁ : ∀ Q, Subsingleton (ι.obj (L.obj Q) ⟶ Tr.obj₃⟦(-1 : ℤ)⟧)) :
    ∃ e₀ : ι.obj (L.obj (R.obj B)) ≅ Tr.obj₁,
      e₀.hom ≫ Tr.mor₁ = ι.map (adj.counit.app B) ≫ e₂.hom := by
  let β : P ⟶ R.obj B := adj.homEquiv _ _ (hι.preimage (e₁.hom ≫ Tr.mor₁ ≫ e₂.inv))
  have h' : L.map β ≫ adj.counit.app B = hι.preimage (e₁.hom ≫ Tr.mor₁ ≫ e₂.inv) := by
    refine (Adjunction.homEquiv_counit adj _ _ β).symm.trans ?_
    exact (adj.homEquiv _ _).symm_apply_apply _
  have hβ : ι.map (L.map β ≫ adj.counit.app B) ≫ e₂.hom = e₁.hom ≫ Tr.mor₁ := by
    rw [h', Functor.FullyFaithful.map_preimage]
    simp
  have := isIso_of_adjunction_triangle_of_fullyFaithful adj hι hL Tr hT e₁ e₂ h₀ h₁ β hβ
  refine ⟨ι.mapIso (L.mapIso (asIso β).symm) ≪≫ e₁, ?_⟩
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_inv, Category.assoc]
  rw [← hβ, ← ι.map_comp_assoc, ← Category.assoc, ← L.map_comp, IsIso.inv_hom_id, L.map_id,
    Category.id_comp]

/-- **Mates of base change isomorphisms and triangles.** Let `L ⊣ R`, `L' ⊣ R'` be adjunctions,
`bc : L ⋙ H ⟶ G ⋙ L'` an isomorphism, `ι : D ⥤ T`, `ι' : D' ⥤ T'` fully faithful functors to
pretriangulated categories with `L ⋙ ι`, `L' ⋙ ι'` fully faithful, and `Φ : T ⥤ T'` a functor
commuting with the shifts with `κ : H ⋙ ι' ≅ ι ⋙ Φ`. Let `Tr` be a distinguished triangle of `T`
with `Tr.obj₁ ≅ ι (L P)` and `Tr.obj₂ ≅ ι B`, whose image under `Φ` is distinguished, and such
that `Tr.obj₃` (resp. `Φ Tr.obj₃`) and its shift by `-1` receive no nonzero maps from the
`ι (L Q)` (resp. `ι' (L' Q)`). Then the mate `R B ⋙ G ⟶ R' (H B)` of `bc⁻¹` is an isomorphism at
`B`: its transpose is the image under `Φ` of the first map of `Tr`. -/
lemma isIso_mateEquiv_inv_app_of_triangle {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {L' : C' ⥤ D'} {R' : D' ⥤ C'} (adj' : L' ⊣ R') {G : C ⥤ C'} {H : D ⥤ D'}
    (bc : L ⋙ H ⟶ G ⋙ L') [IsIso bc] {ι : D ⥤ T} {ι' : D' ⥤ T'} (hι : ι.FullyFaithful)
    (hι' : ι'.FullyFaithful) (hL : (L ⋙ ι).FullyFaithful) (hL' : (L' ⋙ ι').FullyFaithful)
    (Φ : T ⥤ T') [Φ.CommShift ℤ] (κ : H ⋙ ι' ≅ ι ⋙ Φ) (Tr : Triangle T)
    (hT : Tr ∈ distTriang T) (hT' : Φ.mapTriangle.obj Tr ∈ distTriang T') {P : C} {B : D}
    (e₁ : ι.obj (L.obj P) ≅ Tr.obj₁) (e₂ : ι.obj B ≅ Tr.obj₂)
    (h₀ : ∀ Q, Subsingleton (ι.obj (L.obj Q) ⟶ Tr.obj₃))
    (h₁ : ∀ Q, Subsingleton (ι.obj (L.obj Q) ⟶ Tr.obj₃⟦(-1 : ℤ)⟧))
    (h₀' : ∀ Q, Subsingleton (ι'.obj (L'.obj Q) ⟶ (Φ.mapTriangle.obj Tr).obj₃))
    (h₁' : ∀ Q, Subsingleton (ι'.obj (L'.obj Q) ⟶ (Φ.mapTriangle.obj Tr).obj₃⟦(-1 : ℤ)⟧)) :
    IsIso ((mateEquiv adj adj' (inv bc)).app B) := by
  obtain ⟨e₀, he₀⟩ := exists_iso_counit_comp_eq_mor₁ adj hι hL Tr hT e₁ e₂ h₀ h₁
  let e₁' : ι'.obj (L'.obj (G.obj (R.obj B))) ≅ (Φ.mapTriangle.obj Tr).obj₁ :=
    ι'.mapIso (asIso (bc.app (R.obj B))).symm ≪≫ κ.app (L.obj (R.obj B)) ≪≫ Φ.mapIso e₀
  let e₂' : ι'.obj (H.obj B) ≅ (Φ.mapTriangle.obj Tr).obj₂ := κ.app B ≪≫ Φ.mapIso e₂
  refine isIso_of_adjunction_triangle_of_fullyFaithful adj' hι' hL' _ hT' e₁' e₂' h₀' h₁' _ ?_
  have hκ : ι'.map (H.map (adj.counit.app B)) ≫ κ.hom.app B =
      κ.hom.app (L.obj (R.obj B)) ≫ Φ.map (ι.map (adj.counit.app B)) :=
    κ.hom.naturality (adj.counit.app B)
  rw [mateEquiv_counit, Functor.map_comp]
  simp only [e₁', e₂', Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_inv, Iso.app_hom,
    Category.assoc]
  rw [reassoc_of% hκ, ← Φ.map_comp, ← he₀, Φ.map_comp, NatIso.isIso_inv_app]
  rfl

end CategoryTheory.Pretriangulated

namespace CategoryTheory.Adjunction

variable {DZ DX DP DZ' DX' DP' : Type*} [Category* DZ] [Category* DX] [Category* DP]
  [Category* DZ'] [Category* DX'] [Category* DP']

/-- **Base change of traces along a proper morphism**, in abstract categories. Let
`f_* ⊣ f^!`, `f'_* ⊣ f'^!` be adjunctions, `a_{X*}`, `a_{Z*}`, `a_{X'*}`, `a_{Z'*}` functors with
`f_* ⋙ a_{X*} ≅ a_{Z*}` (`c`) and `f'_* ⋙ a_{X'*} ≅ a_{Z'*}` (`c'`), and base change maps
`bcf : f_* π_X ⟶ π_Z f'_*` (invertible), `bcX`, `bcZ` which paste (`hpaste`). Let `trX`, `trZ`,
`trX'`, `trZ'` be traces with values in `U`, `U'`, related by the composition laws `hρ`, `hρ'`
through `ρ : f^! ωX ≅ ωZ`, `ρ' : f'^! ωX' ≅ ωZ'`, and `φX : πX ωX ⟶ ωX'` compatible with `trX`,
`trX'` through `bcX` and `e : πs U ⟶ U'`. Then
`πZ(ρ⁻¹) ≫ γ(ωX) ≫ f'^!(φX) ≫ ρ'` is compatible with `trZ`, `trZ'` through `bcZ` and `e`, for
`γ` the mate of `bcf⁻¹`. -/
lemma app_comp_map_comp_trace_of_paste {fs : DZ ⥤ DX} {fsh : DX ⥤ DZ} (adjf : fs ⊣ fsh)
    {fs' : DZ' ⥤ DX'} {fsh' : DX' ⥤ DZ'} (adjf' : fs' ⊣ fsh') {aXs : DX ⥤ DP} {aZs : DZ ⥤ DP}
    {aXs' : DX' ⥤ DP'} {aZs' : DZ' ⥤ DP'} {πZ : DZ ⥤ DZ'} {πX : DX ⥤ DX'} {πs : DP ⥤ DP'}
    (bcf : fs ⋙ πX ⟶ πZ ⋙ fs') [IsIso bcf] (bcX : aXs ⋙ πs ⟶ πX ⋙ aXs')
    (bcZ : aZs ⋙ πs ⟶ πZ ⋙ aZs') (c : fs ⋙ aXs ≅ aZs) (c' : fs' ⋙ aXs' ≅ aZs')
    (hpaste : ∀ N, bcZ.app N ≫ c'.inv.app (πZ.obj N) =
      πs.map (c.inv.app N) ≫ bcX.app (fs.obj N) ≫ aXs'.map (bcf.app N))
    {U : DP} {U' : DP'} (e : πs.obj U ⟶ U') {ωX : DX} {ωZ : DZ} {ωX' : DX'} {ωZ' : DZ'}
    (trX : aXs.obj ωX ⟶ U) (trZ : aZs.obj ωZ ⟶ U) (trX' : aXs'.obj ωX' ⟶ U')
    (trZ' : aZs'.obj ωZ' ⟶ U') (ρ : fsh.obj ωX ≅ ωZ) (ρ' : fsh'.obj ωX' ≅ ωZ')
    (hρ : aZs.map ρ.hom ≫ trZ = c.inv.app (fsh.obj ωX) ≫ aXs.map (adjf.counit.app ωX) ≫ trX)
    (hρ' : aZs'.map ρ'.hom ≫ trZ' =
      c'.inv.app (fsh'.obj ωX') ≫ aXs'.map (adjf'.counit.app ωX') ≫ trX')
    (φX : πX.obj ωX ⟶ ωX') (hX : bcX.app ωX ≫ aXs'.map φX ≫ trX' = πs.map trX ≫ e) :
    bcZ.app ωZ ≫ aZs'.map (πZ.map ρ.inv ≫ (mateEquiv adjf adjf' (inv bcf)).app ωX ≫
        fsh'.map φX ≫ ρ'.hom) ≫ trZ' = πs.map trZ ≫ e := by
  have h₁ : bcZ.app ωZ ≫ aZs'.map (πZ.map ρ.inv) =
      πs.map (aZs.map ρ.inv) ≫ bcZ.app (fsh.obj ωX) := (bcZ.naturality ρ.inv).symm
  have h₂ : fs'.map ((mateEquiv adjf adjf' (inv bcf)).app ωX) ≫ adjf'.counit.app (πX.obj ωX) =
      (inv bcf).app (fsh.obj ωX) ≫ πX.map (adjf.counit.app ωX) := mateEquiv_counit _ _ _ _
  have h₃ : fs'.map (fsh'.map φX) ≫ adjf'.counit.app ωX' = adjf'.counit.app (πX.obj ωX) ≫ φX :=
    adjf'.counit.naturality φX
  have h₄ : bcX.app (fs.obj (fsh.obj ωX)) ≫ aXs'.map (πX.map (adjf.counit.app ωX)) =
      πs.map (aXs.map (adjf.counit.app ωX)) ≫ bcX.app ωX := (bcX.naturality _).symm
  have h₅ : πs.map (aZs.map ρ.inv) ≫ πs.map (c.inv.app (fsh.obj ωX)) ≫
      πs.map (aXs.map (adjf.counit.app ωX)) ≫ πs.map trX = πs.map trZ := by
    simp only [← πs.map_comp, ← hρ, ← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id,
      Category.id_comp]
  simp only [Functor.map_comp, Category.assoc, hρ', reassoc_of% h₁]
  rw [c'.inv.naturality_assoc, c'.inv.naturality_assoc, reassoc_of% (hpaste (fsh.obj ωX))]
  simp only [Functor.comp_map, ← aXs'.map_comp_assoc, h₃, reassoc_of% h₂,
    NatIso.isIso_inv_app, IsIso.hom_inv_id_assoc]
  simp only [Functor.map_comp, Category.assoc, reassoc_of% h₄, hX, reassoc_of% h₅]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### The base change map of the exceptional inverse image -/

section BaseChange

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)]

/-- The adjunction `Rf_* ⊣ Rf^!` for a proper morphism `f` of separated schemes of finite type
over a field: the adjunction `Rf_! ⊣ Rf^!` read through `Rf_! ≅ Rf_*`. -/
noncomputable def lowerStarUpperShriekAdjunction {Z P : Over (Spec (.of k₁))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom] (f : Z ⟶ P)
    [IsProper f.left] :
    boundedConstructibleLowerStar ℓ f ⊣ boundedConstructibleUpperShriek ℓ f :=
  (boundedConstructibleUpperShriekAdjunction ℓ f).ofNatIsoLeft
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f)

variable {Z P : Over (Spec (.of k₁))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  {Z' P' : Over (Spec (.of k₂))} [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom]
  [IsSeparated Z'.hom] [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  {f : Z ⟶ P} {f' : Z' ⟶ P'} [IsProper f.left] [IsProper f'.left]
  {πP : P'.left ⟶ P.left} {πZ : Z'.left ⟶ Z.left}

/-- The **base change map of the exceptional inverse image** `πZ^* Rf^! ⟶ Rf'^! πP^*` for a
cartesian square `πZ ≫ f = f' ≫ πP` of schemes of finite type over possibly different fields,
`f` and `f'` proper: the mate, under `Rf_* ⊣ Rf^!` and `Rf'_* ⊣ Rf'^!`, of the inverse of the
proper base change isomorphism `πP^* Rf_* ≅ Rf'_* πZ^*`
(`ProEtale.CondensedRing.boundedConstructibleBaseChangeOfMap`). -/
noncomputable def upperShriekBaseChangeOfMap (sqf : IsPullback πZ f'.left f.left πP) :
    boundedConstructibleUpperShriek ℓ f ⋙ boundedConstructibleUpperStarOfMap ℓ πZ ⟶
      boundedConstructibleUpperStarOfMap ℓ πP ⋙ boundedConstructibleUpperShriek ℓ f' :=
  have := isIso_boundedConstructibleBaseChangeOfMap ℓ sqf
  (mateEquiv (lowerStarUpperShriekAdjunction ℓ f) (lowerStarUpperShriekAdjunction ℓ f')
    (inv (boundedConstructibleBaseChangeOfMap ℓ sqf.toCommSq)))

/-- `ProEtale.CondensedRing.upperShriekBaseChangeOfMap` is the mate of the inverse of the proper
base change isomorphism. -/
lemma upperShriekBaseChangeOfMap_app_eq (sqf : IsPullback πZ f'.left f.left πP)
    (M : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (upperShriekBaseChangeOfMap ℓ sqf).app M =
      haveI := isIso_boundedConstructibleBaseChangeOfMap ℓ sqf
      (mateEquiv (lowerStarUpperShriekAdjunction ℓ f) (lowerStarUpperShriekAdjunction ℓ f')
        (inv (boundedConstructibleBaseChangeOfMap ℓ sqf.toCommSq))).app M :=
  rfl

/-- The **counit compatibility** of `ProEtale.CondensedRing.upperShriekBaseChangeOfMap`: the
transpose of `πZ^* Rf^! M ⟶ Rf'^! πP^* M` under `Rf'_* ⊣ Rf'^!` is `πP^*` of the counit at `M`,
read through proper base change. -/
lemma lowerStar_map_upperShriekBaseChangeOfMap_app_comp_counit
    (sqf : IsPullback πZ f'.left f.left πP) (M : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerStar ℓ f').map ((upperShriekBaseChangeOfMap ℓ sqf).app M) ≫
        (lowerStarUpperShriekAdjunction ℓ f').counit.app
          ((boundedConstructibleUpperStarOfMap ℓ πP).obj M) =
      haveI := isIso_boundedConstructibleBaseChangeOfMap ℓ sqf
      (inv (boundedConstructibleBaseChangeOfMap ℓ sqf.toCommSq)).app
          ((boundedConstructibleUpperShriek ℓ f).obj M) ≫
        (boundedConstructibleUpperStarOfMap ℓ πP).map
          ((lowerStarUpperShriekAdjunction ℓ f).counit.app M) := by
  have := isIso_boundedConstructibleBaseChangeOfMap ℓ sqf
  exact mateEquiv_counit _ _ _ M

end BaseChange

/-! ### Vertical pasting of proper base change maps -/

section Paste

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)]
  {Z X S : Over (Spec (.of k₁))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
  {Z' X' S' : Over (Spec (.of k₂))} [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom]
  [IsSeparated Z'.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType S'.hom] [QuasiCompact S'.hom] [IsSeparated S'.hom]
  {f : Z ⟶ X} {aX : X ⟶ S} {aZ : Z ⟶ S} {f' : Z' ⟶ X'} {aX' : X' ⟶ S'} {aZ' : Z' ⟶ S'}
  {πZ : Z'.left ⟶ Z.left} {πX : X'.left ⟶ X.left} {πS : S'.left ⟶ S.left}

set_option hygiene false in
/-- The coefficient ring `ℚ̲̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj.{u} ℓ

/-- The vertical pasting law on bounded constructible complexes, for arbitrary ambient
transformations `χZ`, `χX`, `χf` and composition maps `κ`, `κ'` satisfying the ambient law; they
are kept abstract so that the kernel never unfolds the base change morphisms. -/
private lemma liftExchange_paste_aux (w : f ≫ aX = aZ) (w' : f' ≫ aX' = aZ')
    (χZ : R((aZ.left)_*⟦𝐐⟧) ⋙ L((πS)^*⟦𝐐⟧) ⟶ L((πZ)^*⟦𝐐⟧) ⋙ R((aZ'.left)_*⟦𝐐⟧))
    (χX : R((aX.left)_*⟦𝐐⟧) ⋙ L((πS)^*⟦𝐐⟧) ⟶ L((πX)^*⟦𝐐⟧) ⋙ R((aX'.left)_*⟦𝐐⟧))
    (χf : R((f.left)_*⟦𝐐⟧) ⋙ L((πX)^*⟦𝐐⟧) ⟶ L((πZ)^*⟦𝐐⟧) ⋙ R((f'.left)_*⟦𝐐⟧))
    (κ : R((aZ.left)_*⟦𝐐⟧) ⟶ R((f.left)_*⟦𝐐⟧) ⋙ R((aX.left)_*⟦𝐐⟧))
    (κ' : R((aZ'.left)_*⟦𝐐⟧) ⟶ R((f'.left)_*⟦𝐐⟧) ⋙ R((aX'.left)_*⟦𝐐⟧))
    (hκ : ∀ N, ((boundedConstructibleLowerStarCompOfEq ℓ f aX w).inv.app N).hom = κ.app N.obj)
    (hκ' : ∀ N, ((boundedConstructibleLowerStarCompOfEq ℓ f' aX' w').inv.app N).hom =
      κ'.app N.obj)
    (h : ∀ N, χZ.app N ≫ κ'.app (L((πZ)^*⟦𝐐⟧).obj N) =
      L((πS)^*⟦𝐐⟧).map (κ.app N) ≫ χX.app (R((f.left)_*⟦𝐐⟧).obj N) ≫
        R((aX'.left)_*⟦𝐐⟧).map (χf.app N))
    (N : Dᵇc(Z.left)⟦𝐐⟧) :
    (NearbyCyclesModel.liftExchange χZ
        (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ aZ K)
        (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ aZ' K)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ πS K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ πZ K.obj K.property) :
          boundedConstructibleLowerStar ℓ aZ ⋙ boundedConstructibleUpperStarOfMap ℓ πS ⟶
            boundedConstructibleUpperStarOfMap ℓ πZ ⋙ boundedConstructibleLowerStar ℓ aZ').app N ≫
        (boundedConstructibleLowerStarCompOfEq ℓ f' aX' w').inv.app
          ((boundedConstructibleUpperStarOfMap ℓ πZ).obj N) =
      (boundedConstructibleUpperStarOfMap ℓ πS).map
          ((boundedConstructibleLowerStarCompOfEq ℓ f aX w).inv.app N) ≫
        (NearbyCyclesModel.liftExchange χX
          (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ aX K)
          (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ aX' K)
          (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ πS K.obj K.property)
          (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ πX K.obj K.property) :
            boundedConstructibleLowerStar ℓ aX ⋙ boundedConstructibleUpperStarOfMap ℓ πS ⟶
              boundedConstructibleUpperStarOfMap ℓ πX ⋙ boundedConstructibleLowerStar ℓ aX').app
          ((boundedConstructibleLowerStar ℓ f).obj N) ≫
        (boundedConstructibleLowerStar ℓ aX').map
          ((NearbyCyclesModel.liftExchange χf
            (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ f K)
            (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ f' K)
            (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ πX K.obj K.property)
            (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ πZ K.obj
              K.property) :
              boundedConstructibleLowerStar ℓ f ⋙ boundedConstructibleUpperStarOfMap ℓ πX ⟶
                boundedConstructibleUpperStarOfMap ℓ πZ ⋙ boundedConstructibleLowerStar ℓ f').app
            N) := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, hκ, hκ',
    boundedConstructibleUpperStarOfMap_map, ObjectProperty.homMk_hom,
    NearbyCyclesModel.liftExchange_app_hom]
  exact h N.obj

/-- **Vertical pasting of base change maps** on bounded constructible complexes: for commutative
squares `πZ ≫ f = f' ≫ πX` and `πX ≫ a_X = a_X' ≫ πS` and their composite
`πZ ≫ a_Z = a_Z' ≫ πS` (`a_Z = f ≫ a_X`, `a_Z' = f' ≫ a_X'`), the base change map of the
composite is that of the lower square on `Rf_*`, followed by `Ra_{X'*}` of that of the upper
square, through the composition isomorphisms `Ra_{Z*} ≅ Ra_{X*} Rf_*`. -/
lemma boundedConstructibleBaseChangeOfMap_app_comp_lowerStarCompOfEq_inv_app
    (w : f ≫ aX = aZ) (w' : f' ≫ aX' = aZ') (sqf : CommSq πZ f'.left f.left πX)
    (sqX : CommSq πX aX'.left aX.left πS) (sqZ : CommSq πZ aZ'.left aZ.left πS)
    (N : Dᵇc(Z.left)⟦𝐐⟧) :
    (boundedConstructibleBaseChangeOfMap ℓ sqZ).app N ≫
        (boundedConstructibleLowerStarCompOfEq ℓ f' aX' w').inv.app
          ((boundedConstructibleUpperStarOfMap ℓ πZ).obj N) =
      (boundedConstructibleUpperStarOfMap ℓ πS).map
          ((boundedConstructibleLowerStarCompOfEq ℓ f aX w).inv.app N) ≫
        (boundedConstructibleBaseChangeOfMap ℓ sqX).app
          ((boundedConstructibleLowerStar ℓ f).obj N) ≫
        (boundedConstructibleLowerStar ℓ aX').map
          ((boundedConstructibleBaseChangeOfMap ℓ sqf).app N) := by
  have hamb : ∀ K, (baseChangeMap 𝐐 sqZ).app K ≫
      (conjugateIsoEquiv (derivedUpperStarLowerStarAdjunction 𝐐 aZ'.left)
        ((derivedUpperStarLowerStarAdjunction 𝐐 aX'.left).comp
          (derivedUpperStarLowerStarAdjunction 𝐐 f'.left))
        (leftDerivedUpperStarCompOfEq 𝐐 (congrArg CommaMorphism.left w')).symm).hom.app
          (L((πZ)^*⟦𝐐⟧).obj K) =
      L((πS)^*⟦𝐐⟧).map ((conjugateIsoEquiv (derivedUpperStarLowerStarAdjunction 𝐐 aZ.left)
        ((derivedUpperStarLowerStarAdjunction 𝐐 aX.left).comp
          (derivedUpperStarLowerStarAdjunction 𝐐 f.left))
        (leftDerivedUpperStarCompOfEq 𝐐 (congrArg CommaMorphism.left w)).symm).hom.app K) ≫
        (baseChangeMap 𝐐 sqX).app (R((f.left)_*⟦𝐐⟧).obj K) ≫
          R((aX'.left)_*⟦𝐐⟧).map ((baseChangeMap 𝐐 sqf).app K) := fun K ↦
    mateEquiv_comp_aux (derivedUpperStarLowerStarAdjunction _ aX.left)
      (derivedUpperStarLowerStarAdjunction _ f.left)
      (derivedUpperStarLowerStarAdjunction _ aZ.left)
      (derivedUpperStarLowerStarAdjunction _ aX'.left)
      (derivedUpperStarLowerStarAdjunction _ f'.left)
      (derivedUpperStarLowerStarAdjunction _ aZ'.left)
      (leftDerivedUpperStarCompOfEq _ (congrArg CommaMorphism.left w))
      (leftDerivedUpperStarCompOfEq _ (congrArg CommaMorphism.left w'))
      (pullbackSquareComparison _ sqX).hom (pullbackSquareComparison _ sqf).hom
      (pullbackSquareComparison _ sqZ).hom
      (fun K ↦ (pullbackSquareComparison_hom_app_paste_of_eq _ sqf sqX _ _ sqZ K).symm)
      (baseChangeMap _ sqX) (Adjunction.exchangeRight_eq_mateEquiv _ _ _)
      (baseChangeMap _ sqf) (Adjunction.exchangeRight_eq_mateEquiv _ _ _)
      (baseChangeMap _ sqZ) (Adjunction.exchangeRight_eq_mateEquiv _ _ _) K
  have := liftExchange_paste_aux ℓ w w' (baseChangeMap _ sqZ) (baseChangeMap _ sqX)
    (baseChangeMap _ sqf) _ _ (boundedConstructibleLowerStarCompOfEq_inv_app_hom ℓ f aX aZ w)
    (boundedConstructibleLowerStarCompOfEq_inv_app_hom ℓ f' aX' aZ' w') hamb N
  unfold boundedConstructibleBaseChangeOfMap
  cast_proofs this
end Paste

/-! ### Closed immersions and field extensions -/

section Closed

set_option hygiene false in
/-- The coefficient ring `ℚ̲̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj.{u} ℓ

variable (ℓ : ℕ) [Fact ℓ.Prime] {F L : Type u} [Field F] [Field L] [Algebra F L]
  [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)] [Fact (ringChar L).Prime]
  [Fact (ringChar L ≠ ℓ)]
  {P Z : Over (Spec (.of F))} [LocallyOfFiniteType P.hom] [QuasiCompact P.hom]
  [IsSeparated P.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  {P' Z' : Over (Spec (.of L))} [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom]
  [IsSeparated P'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  {i : Z ⟶ P} {i' : Z' ⟶ P'} [IsClosedImmersion i.left] [IsClosedImmersion i'.left]
  {πP : P'.left ⟶ P.left} {πZ : Z'.left ⟶ Z.left}

/-- **The base change map of a closed exceptional inverse image along a field extension is an
isomorphism**: for a closed immersion `i : Z ⟶ P` of separated `F`-schemes of finite type, its
base change `i' : Z' ⟶ P'` along a field extension `F ⟶ L` and a bounded constructible
`ℚ̄_ℓ`-complex `M` on `P`, the canonical map `πZ^* Ri^! M ⟶ Ri'^! πP^* M` is invertible. -/
theorem isIso_upperShriekBaseChangeOfMap_app_of_fieldExtension
    (hP : IsPullback πP P'.hom P.hom (Spec.map (CommRingCat.ofHom (algebraMap F L))))
    (sq : IsPullback πZ i'.left i.left πP) (M : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((upperShriekBaseChangeOfMap ℓ sq).app M) := by
  /- The open complement `V` of `i` and its preimage `V'` in `P'`. -/
  let V : P.left.Opens :=
    ⟨(Set.range i.left.base)ᶜ, i.left.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have : TopologicalSpace.NoetherianSpace V := V.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact V.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hV : Set.range V.ι.base = (Set.range i.left.base)ᶜ := Scheme.Opens.range_ι V
  have hcompl : IsCompl (Set.range i.left.base) (Set.range V.ι.base) := by
    rw [hV]
    exact isCompl_compl
  let V' : P'.left.Opens := πP ⁻¹ᵁ V
  have : TopologicalSpace.NoetherianSpace V' :=
    V'.ι.isOpenEmbedding.isInducing.noetherianSpace
  have hV' : Disjoint (Set.range V'.ι.base) (Set.range i'.left.base) := by
    rw [Scheme.Opens.range_ι, Set.disjoint_left]
    rintro _ hx ⟨z, rfl⟩
    have hx' : πP.base (i'.left.base z) ∉ Set.range i.left.base := hx
    refine hx' ⟨πZ.base z, ?_⟩
    rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply]
  have sqV : IsPullback (πP ∣_ V) V'.ι V.ι πP := isPullback_morphismRestrict πP V
  /- The triangle `X ⟶ M ⟶ Rj_* j^* M ⟶`. -/
  let adjV := derivedUpperStarLowerStarAdjunction 𝐐 V.ι
  obtain ⟨X, f, h, hT⟩ := distinguished_cocone_triangle₁ (adjV.unit.app M.obj)
  have hjX := isZero_map_obj_of_distinguished_unit_triangle adjV f h hT
  have hiX : IsIso ((derivedUpperStarLowerStarAdjunction 𝐐 i.left).unit.app X) :=
    isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero _ V.ι i.left hcompl hjX
  have : LocallyOfFiniteType (Over.mk (V.ι ≫ P.hom)).hom :=
    inferInstanceAs (LocallyOfFiniteType (V.ι ≫ P.hom))
  have : QuasiCompact (Over.mk (V.ι ≫ P.hom)).hom :=
    inferInstanceAs (QuasiCompact (V.ι ≫ P.hom))
  have : IsSeparated (Over.mk (V.ι ≫ P.hom)).hom :=
    inferInstanceAs (IsSeparated (V.ι ≫ P.hom))
  have hjM := boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ V.ι M.obj M.property
  have hRj := boundedConstructible_rightDerivedLowerStar_obj ℓ
    (Over.homMk V.ι : Over.mk (V.ι ≫ P.hom) ⟶ P) ⟨_, hjM⟩
  have hX : boundedConstructible _ X :=
    (boundedConstructible _).ext_of_isTriangulatedClosed₁ _ hT M.property hRj
  /- The closed part `Q₀ = Li^* X`, with `Ri_* Q₀ ≅ X`. -/
  let Q₀ : Dᵇc(Z.left)⟦𝐐⟧ :=
    ⟨(L((i.left)^*⟦𝐐⟧)).obj X,
      boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ i.left X hX⟩
  let e₁ : (boundedConstructible _).ι.obj ((boundedConstructibleLowerStar ℓ i).obj Q₀) ≅ X :=
    (asIso ((derivedUpperStarLowerStarAdjunction 𝐐 i.left).unit.app X)).symm
  have hLi : (boundedConstructibleLowerStar ℓ i ⋙ (boundedConstructible _).ι).FullyFaithful :=
    ((ObjectProperty.fullyFaithfulι _).comp
      (derivedUpperStarLowerStarAdjunction 𝐐 i.left).fullyFaithfulROfIsIsoCounit).ofIso
      (boundedConstructibleLowerStarCompatibility ℓ i).symm
  have hLi' : (boundedConstructibleLowerStar ℓ i' ⋙ (boundedConstructible _).ι).FullyFaithful :=
    ((ObjectProperty.fullyFaithfulι _).comp
      (derivedUpperStarLowerStarAdjunction 𝐐 i'.left).fullyFaithfulROfIsIsoCounit).ofIso
      (boundedConstructibleLowerStarCompatibility ℓ i').symm
  /- The pulled back triangle. -/
  let Tr := Triangle.mk f (adjV.unit.app M.obj) h
  have hT' : (L((πP)^*⟦𝐐⟧)).mapTriangle.obj Tr ∈ distTriang _ :=
    (L((πP)^*⟦𝐐⟧)).map_distinguished _ hT
  have : IsLocallyNoetherian P.left := LocallyOfFiniteType.isLocallyNoetherian P.hom
  have : IsNoetherian V.toScheme := {}
  have hbcU : IsIso ((baseChangeMap 𝐐 sqV.toCommSq).app ((L((V.ι)^*⟦𝐐⟧)).obj M.obj)) := by
    exact_mod_proofs isIso_baseChangeMap_app_padicAlgCl_of_fieldExtension P.hom P'.hom hP ℓ sqV
      (isUnit_natCast_spec ℓ F) _ hjM
  let e₃ := asIso ((baseChangeMap 𝐐 sqV.toCommSq).app ((L((V.ι)^*⟦𝐐⟧)).obj M.obj))
  have := isIso_boundedConstructibleBaseChangeOfMap ℓ sq
  exact isIso_mateEquiv_inv_app_of_triangle (lowerStarUpperShriekAdjunction ℓ i)
    (lowerStarUpperShriekAdjunction ℓ i') (boundedConstructibleBaseChangeOfMap ℓ sq.toCommSq)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _) hLi hLi'
    (L((πP)^*⟦𝐐⟧)) (ObjectProperty.liftCompιIso _ _ _) Tr hT hT' e₁ (Iso.refl _)
    (fun Q ↦ adjV.subsingleton_hom_of_isZero
      (isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj_of_disjoint _ V.ι i.left
        hcompl.symm.disjoint Q.obj) _)
    (fun Q ↦ subsingleton_hom_rightDerivedLowerStar_shift_of_disjoint _ V.ι i.left
        hcompl.symm.disjoint Q.obj _ _)
    (fun Q ↦ @Equiv.subsingleton _ _ (Iso.homCongr (Iso.refl _) e₃)
      ((derivedUpperStarLowerStarAdjunction 𝐐 V'.ι).subsingleton_hom_of_isZero
        (isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj_of_disjoint _ V'.ι i'.left
          hV' Q.obj) _))
    (fun Q ↦ @Equiv.subsingleton _ _
      (Iso.homCongr (Iso.refl _) ((shiftFunctor _ (-1 : ℤ)).mapIso e₃))
      (subsingleton_hom_rightDerivedLowerStar_shift_of_disjoint _ V'.ι i'.left hV' Q.obj _ _))

end Closed

/-! ### Composition with the comparison of dualizing complexes -/

section Dualizing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)]
  {X Z : Over (Spec (.of k₁))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [IsProper (toPoint X).left] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [IsProper (toPoint Z).left]
  {X' Z' : Over (Spec (.of k₂))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [IsProper (toPoint X').left] [LocallyOfFiniteType Z'.hom]
  [QuasiCompact Z'.hom] [IsSeparated Z'.hom] [IsProper (toPoint Z').left]
  {f : Z ⟶ X} {f' : Z' ⟶ X'} [IsProper f.left] [IsProper f'.left]
  {πX : X'.left ⟶ X.left} {πZ : Z'.left ⟶ Z.left} {πₛ : Spec (.of k₂) ⟶ Spec (.of k₁)}
  (e : (boundedConstructibleUpperStarOfMap ℓ (X := point k₁) (Y := point k₂) πₛ).obj (𝟙_ _) ⟶
    𝟙_ _)

omit [IsProper (toPoint X').left] [IsProper (toPoint Z').left] [IsProper f'.left] in
/-- The composition of traces
`ProEtale.CondensedRing.lowerStar_map_upperShriekDualizingComplexIso_hom_comp_trace`, with the
counit of `Rf_* ⊣ Rf^!` (`ProEtale.CondensedRing.lowerStarUpperShriekAdjunction`). -/
lemma lowerStar_map_upperShriekDualizingComplexIso_hom_comp_trace' :
    (boundedConstructibleLowerStar ℓ (toPoint Z)).map (upperShriekDualizingComplexIso ℓ f).hom ≫
        NearbyCyclesModel.trace ℓ Z =
      (boundedConstructibleLowerStarCompOfEq ℓ f (toPoint X) (comp_toPoint f)).inv.app
          ((boundedConstructibleUpperShriek ℓ f).obj (dualizingComplex ℓ X)) ≫
        (boundedConstructibleLowerStar ℓ (toPoint X)).map
          ((lowerStarUpperShriekAdjunction ℓ f).counit.app (dualizingComplex ℓ X)) ≫
        NearbyCyclesModel.trace ℓ X := by
  exact_mod_proofs lowerStar_map_upperShriekDualizingComplexIso_hom_comp_trace ℓ f

/-- **The comparison of dualizing complexes and proper morphisms**: for a proper morphism
`f : Z ⟶ X` of proper `k₁`-schemes and its base change `f' : Z' ⟶ X'` along `πₛ`, the comparison
`φ_Z : πZ^* ω_Z ⟶ ω_{Z'}` is `πZ^* ω_Z ≅ πZ^* Rf^! ω_X ⟶ Rf'^! πX^* ω_X ⟶ Rf'^! ω_{X'} ≅ ω_{Z'}`,
through the base change map of the exceptional inverse image
(`ProEtale.CondensedRing.upperShriekBaseChangeOfMap`) and `Rf'^!(φ_X)`. -/
theorem dualizingComplexBaseChange_eq_comp_upperShriekBaseChangeOfMap
    (sqX : IsPullback πX (toPoint X').left (toPoint X).left πₛ)
    (sqZ : IsPullback πZ (toPoint Z').left (toPoint Z).left πₛ)
    (sqf : IsPullback πZ f'.left f.left πX) :
    dualizingComplexBaseChange ℓ e sqZ =
      (boundedConstructibleUpperStarOfMap ℓ πZ).map (upperShriekDualizingComplexIso ℓ f).inv ≫
        (upperShriekBaseChangeOfMap ℓ sqf).app (dualizingComplex ℓ X) ≫
        (boundedConstructibleUpperShriek ℓ f').map (dualizingComplexBaseChange ℓ e sqX) ≫
        (upperShriekDualizingComplexIso ℓ f').hom := by
  have := isIso_boundedConstructibleBaseChangeOfMap ℓ sqf
  rw [upperShriekBaseChangeOfMap_app_eq]
  have h := Adjunction.app_comp_map_comp_trace_of_paste (lowerStarUpperShriekAdjunction ℓ f)
    (lowerStarUpperShriekAdjunction ℓ f') (boundedConstructibleBaseChangeOfMap ℓ sqf.toCommSq)
    (boundedConstructibleBaseChangeOfMap ℓ sqX.toCommSq)
    (boundedConstructibleBaseChangeOfMap ℓ sqZ.toCommSq)
    (boundedConstructibleLowerStarCompOfEq ℓ f (toPoint X) (comp_toPoint f))
    (boundedConstructibleLowerStarCompOfEq ℓ f' (toPoint X') (comp_toPoint f'))
    (boundedConstructibleBaseChangeOfMap_app_comp_lowerStarCompOfEq_inv_app ℓ _ _
      sqf.toCommSq sqX.toCommSq sqZ.toCommSq)
    e (NearbyCyclesModel.trace ℓ X) (NearbyCyclesModel.trace ℓ Z)
    (NearbyCyclesModel.trace ℓ X') (NearbyCyclesModel.trace ℓ Z')
    (upperShriekDualizingComplexIso ℓ f) (upperShriekDualizingComplexIso ℓ f')
    (lowerStar_map_upperShriekDualizingComplexIso_hom_comp_trace' ℓ (f := f))
    (lowerStar_map_upperShriekDualizingComplexIso_hom_comp_trace' ℓ (f := f'))
    (dualizingComplexBaseChange ℓ e sqX)
    (baseChange_comp_map_dualizingComplexBaseChange_comp_trace ℓ e sqX)
  exact (eq_dualizingComplexBaseChange_of_trace ℓ e sqZ h).symm


/-- `ProEtale.CondensedRing.dualizingComplexBaseChange_eq_comp_upperShriekBaseChangeOfMap`, read
through the composition isomorphisms `Rf^! ω_X ≅ ω_Z` and `Rf'^! ω_{X'} ≅ ω_{Z'}`:
`φ_Z ∘ ρ' ⁻¹ = Rf'^!(φ_X) ∘ γ(ω_X) ∘ πZ^*(ρ⁻¹)`. -/
theorem dualizingComplexBaseChange_comp_upperShriekDualizingComplexIso_inv
    (sqX : IsPullback πX (toPoint X').left (toPoint X).left πₛ)
    (sqZ : IsPullback πZ (toPoint Z').left (toPoint Z).left πₛ)
    (sqf : IsPullback πZ f'.left f.left πX) :
    dualizingComplexBaseChange ℓ e sqZ ≫ (upperShriekDualizingComplexIso ℓ f').inv =
      (boundedConstructibleUpperStarOfMap ℓ πZ).map (upperShriekDualizingComplexIso ℓ f).inv ≫
        (upperShriekBaseChangeOfMap ℓ sqf).app (dualizingComplex ℓ X) ≫
        (boundedConstructibleUpperShriek ℓ f').map (dualizingComplexBaseChange ℓ e sqX) := by
  rw [dualizingComplexBaseChange_eq_comp_upperShriekBaseChangeOfMap ℓ e sqX sqZ sqf]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Dualizing

/-! ### Closed immersions of proper schemes -/

section ClosedDualizing

variable (ℓ : ℕ) [Fact ℓ.Prime] {F L : Type u} [Field F] [Field L] [Algebra F L]
  [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)] [Fact (ringChar L).Prime]
  [Fact (ringChar L ≠ ℓ)]
  {X Z : Over (Spec (.of F))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [IsProper (toPoint X).left] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [IsProper (toPoint Z).left]
  {X' Z' : Over (Spec (.of L))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [IsProper (toPoint X').left] [LocallyOfFiniteType Z'.hom]
  [QuasiCompact Z'.hom] [IsSeparated Z'.hom] [IsProper (toPoint Z').left]
  {i : Z ⟶ X} {i' : Z' ⟶ X'} [IsClosedImmersion i.left] [IsClosedImmersion i'.left]
  {πX : X'.left ⟶ X.left} {πZ : Z'.left ⟶ Z.left}
  (e : (boundedConstructibleUpperStarOfMap ℓ (X := point F) (Y := point L)
    (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj (𝟙_ _) ⟶ 𝟙_ _)

/-- **Base change of dualizing complexes and closed immersions**: for a closed immersion
`i : Z ⟶ X` of proper `F`-schemes and its base change `i' : Z' ⟶ X'` along a field extension
`L/F`, the comparison `φ_Z : πZ^* ω_Z ⟶ ω_{Z'}` of the dualizing complexes is an isomorphism if
and only if `Ri'^!(φ_X)` is. -/
theorem isIso_dualizingComplexBaseChange_iff_of_isClosedImmersion
    (sqX : IsPullback πX (toPoint X').left (toPoint X).left
      (Spec.map (CommRingCat.ofHom (algebraMap F L))))
    (sqZ : IsPullback πZ (toPoint Z').left (toPoint Z).left
      (Spec.map (CommRingCat.ofHom (algebraMap F L))))
    (sqi : IsPullback πZ i'.left i.left πX) :
    IsIso (dualizingComplexBaseChange ℓ e sqZ) ↔
      IsIso ((boundedConstructibleUpperShriek ℓ i').map (dualizingComplexBaseChange ℓ e sqX)) := by
  have hX : IsPullback πX X'.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap F L))) := by
    simpa using sqX
  have := isIso_upperShriekBaseChangeOfMap_app_of_fieldExtension ℓ hX sqi (dualizingComplex ℓ X)
  rw [dualizingComplexBaseChange_eq_comp_upperShriekBaseChangeOfMap ℓ e sqX sqZ sqi]
  refine ⟨fun h ↦ ?_, fun h ↦ inferInstance⟩
  have := IsIso.of_isIso_comp_left
    ((boundedConstructibleUpperStarOfMap ℓ πZ).map (upperShriekDualizingComplexIso ℓ i).inv)
    ((upperShriekBaseChangeOfMap ℓ sqi).app (dualizingComplex ℓ X) ≫
      (boundedConstructibleUpperShriek ℓ i').map (dualizingComplexBaseChange ℓ e sqX) ≫
        (upperShriekDualizingComplexIso ℓ i').hom)
  have := IsIso.of_isIso_comp_left
    ((upperShriekBaseChangeOfMap ℓ sqi).app (dualizingComplex ℓ X))
    ((boundedConstructibleUpperShriek ℓ i').map (dualizingComplexBaseChange ℓ e sqX) ≫
      (upperShriekDualizingComplexIso ℓ i').hom)
  exact IsIso.of_isIso_comp_right _ (upperShriekDualizingComplexIso ℓ i').hom

/-- **Base change of dualizing complexes and closed immersions**: if the comparison `φ_X` of the
dualizing complexes of a proper `F`-scheme `X` along a field extension `L/F` is an isomorphism,
then so is that of every closed subscheme `Z` of `X`. -/
theorem isIso_dualizingComplexBaseChange_of_isClosedImmersion
    (sqX : IsPullback πX (toPoint X').left (toPoint X).left
      (Spec.map (CommRingCat.ofHom (algebraMap F L))))
    (sqZ : IsPullback πZ (toPoint Z').left (toPoint Z).left
      (Spec.map (CommRingCat.ofHom (algebraMap F L))))
    (sqi : IsPullback πZ i'.left i.left πX) [IsIso (dualizingComplexBaseChange ℓ e sqX)] :
    IsIso (dualizingComplexBaseChange ℓ e sqZ) :=
  (isIso_dualizingComplexBaseChange_iff_of_isClosedImmersion ℓ e sqX sqZ sqi).2 inferInstance

end ClosedDualizing

end AlgebraicGeometry.ProEtale.CondensedRing
