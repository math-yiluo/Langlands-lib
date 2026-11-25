/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.FieldExtension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleClosedPushforward
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionFullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerStarFullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Basic
import WeilConjectures.Tactic.ExactModProofs

/-!
# Closed exceptional inverse images commute with base change along field extensions

Let `F ⟶ L` be a field extension, `P` a separated `F`-scheme of finite type with base change
`P' = P ×_F L` (`πP : P' ⟶ P`), `i : Z ⟶ P` a closed immersion and `i' : Z' ⟶ P'` its base change
(`πZ : Z' ⟶ Z`). For every bounded constructible `ℚ̄_ℓ`-complex `M` on `P`
(`ℓ` invertible in `F`) there is an isomorphism
`πZ^* Ri^! M ≅ Ri'^! πP^* M`
(`ProEtale.CondensedRing.nonempty_iso_upperShriek_closedImmersion_of_fieldExtension`).

## Proof

Let `j : U ⟶ P` be the open complement of `i` and `j' : U' ⟶ P'` its base change. Complete the
unit `M ⟶ Rj_* j^* M` to a distinguished triangle `X ⟶ M ⟶ Rj_* j^* M ⟶` of the ambient derived
category. Its restriction to `U` has an invertible second map, so `j^* X = 0` and `X ≅ Ri_* Q₀` for
`Q₀ = Li^* X`, which is bounded constructible. Maps from `Ri_* Q` to the shifts of `Rj_* W` vanish
(`Lj^* Ri_* = 0`), so the formal lemma
`CategoryTheory.Pretriangulated.nonempty_iso_of_adjunction_triangle` (a variant of
`CategoryTheory.Pretriangulated.isIso_of_adjunction_triangle` for full subcategories of a
pretriangulated category) gives `Ri^! M ≅ Q₀`.

Pulling the triangle back along `πP`, the first term becomes
`πP^* Ri_* Q₀ ≅ Ri'_* πZ^* Q₀` (proper base change,
`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicAlgCl_of_isProper`) and the third term
`πP^* Rj_* j^* M ≅ Rj'_* πU^* j^* M` (base change along the field extension,
`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicAlgCl_of_fieldExtension`), which again
receives no maps from the shifts of `Ri'_* Q`. The same formal lemma gives
`Ri'^! πP^* M ≅ πZ^* Q₀ ≅ πZ^* Ri^! M`.

## Main results

- `CategoryTheory.Pretriangulated.isIso_of_adjunction_triangle_of_fullyFaithful`,
  `CategoryTheory.Pretriangulated.nonempty_iso_of_adjunction_triangle`: the formal input.
- `ProEtale.CondensedRing.subsingleton_hom_rightDerivedLowerStar_shift_of_disjoint`: maps from
  `Rc_* B` to the shifts of `Rj_* W` vanish for disjoint closed and open immersions `c`, `j`.
- `ProEtale.CondensedRing.nonempty_iso_upperShriek_closedImmersion_of_fieldExtension`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Pretriangulated

variable {C D T : Type*} [Category* C] [Category* D] [Category* T] [Preadditive T]
  [HasZeroObject T] [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]

/-- Let `L ⊣ R` be an adjunction, `ι : D ⥤ T` a fully faithful functor to a pretriangulated
category such that `L ⋙ ι` is fully faithful, and `Tr` a distinguished triangle of `T` with
`Tr.obj₁ ≅ ι (L P)`, `Tr.obj₂ ≅ ι B` and whose third object receives no nonzero maps from the
objects `ι (L Q)` and `ι (L Q)⟦1⟧`. Then a map `β : P ⟶ R B` whose transpose is `Tr.mor₁` is an
isomorphism. For `ι = 𝟭` this is `CategoryTheory.Pretriangulated.isIso_of_adjunction_triangle`. -/
lemma isIso_of_adjunction_triangle_of_fullyFaithful {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {ι : D ⥤ T} (hι : ι.FullyFaithful) (hL : (L ⋙ ι).FullyFaithful) (Tr : Triangle T)
    (hT : Tr ∈ distTriang T) {P : C} {B : D} (e₁ : ι.obj (L.obj P) ≅ Tr.obj₁)
    (e₂ : ι.obj B ≅ Tr.obj₂) (h₀ : ∀ Q, Subsingleton (ι.obj (L.obj Q) ⟶ Tr.obj₃))
    (h₁ : ∀ Q, Subsingleton (ι.obj (L.obj Q) ⟶ Tr.obj₃⟦(-1 : ℤ)⟧)) (β : P ⟶ R.obj B)
    (hβ : ι.map (L.map β ≫ adj.counit.app B) ≫ e₂.hom = e₁.hom ≫ Tr.mor₁) :
    IsIso β := by
  refine isIso_of_yoneda_map_bijective β fun Q ↦ ?_
  let Φ : (Q ⟶ R.obj B) ≃ (ι.obj (L.obj Q) ⟶ Tr.obj₂) :=
    (adj.homEquiv _ _).symm.trans (hι.homEquiv.trans (Iso.homCongr (Iso.refl _) e₂))
  let Ψ : (Q ⟶ P) ≃ (ι.obj (L.obj Q) ⟶ Tr.obj₁) :=
    hL.homEquiv.trans (Iso.homCongr (Iso.refl _) e₁)
  have key : ∀ x : Q ⟶ P, Φ (x ≫ β) = Ψ x ≫ Tr.mor₁ := by
    intro x
    simp only [Φ, Ψ, Equiv.trans_apply, Adjunction.homEquiv_counit, Iso.homCongr_apply,
      Iso.refl_inv, Functor.FullyFaithful.homEquiv_apply, Functor.comp_map]
    simp only [Category.id_comp, Category.assoc]
    rw [← hβ]
    simp
  have hinj : Function.Injective (fun y : ι.obj (L.obj Q) ⟶ Tr.obj₁ ↦ y ≫ Tr.mor₁) := by
    intro y₁ y₂ h
    rw [← sub_eq_zero]
    have h' : (y₁ - y₂) ≫ (Triangle.invRotate Tr).mor₂ = 0 := by
      simp only [Triangle.invRotate_mor₂, Preadditive.sub_comp]
      exact sub_eq_zero.2 h
    obtain ⟨z, hz⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _ hT) _ h'
    have : z = 0 := (h₁ Q).elim _ _
    rw [hz, this, zero_comp]
  have hsurj : Function.Surjective (fun y : ι.obj (L.obj Q) ⟶ Tr.obj₁ ↦ y ≫ Tr.mor₁) := by
    intro y
    obtain ⟨z, hz⟩ := Triangle.coyoneda_exact₂ Tr hT y ((h₀ Q).elim _ _)
    exact ⟨z, hz.symm⟩
  have h : (fun x : Q ⟶ P ↦ x ≫ β) =
      Φ.symm ∘ (fun y : ι.obj (L.obj Q) ⟶ Tr.obj₁ ↦ y ≫ Tr.mor₁) ∘ Ψ := by
    funext x
    simp [← key]
  rw [h]
  exact Φ.symm.bijective.comp (⟨hinj, hsurj⟩ : Function.Bijective _) |>.comp Ψ.bijective

/-- Under the hypotheses of
`CategoryTheory.Pretriangulated.isIso_of_adjunction_triangle_of_fullyFaithful`, `R B ≅ P`. -/
lemma nonempty_iso_of_adjunction_triangle {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {ι : D ⥤ T} (hι : ι.FullyFaithful) (hL : (L ⋙ ι).FullyFaithful) (Tr : Triangle T)
    (hT : Tr ∈ distTriang T) {P : C} {B : D} (e₁ : ι.obj (L.obj P) ≅ Tr.obj₁)
    (e₂ : ι.obj B ≅ Tr.obj₂) (h₀ : ∀ Q, Subsingleton (ι.obj (L.obj Q) ⟶ Tr.obj₃))
    (h₁ : ∀ Q, Subsingleton (ι.obj (L.obj Q) ⟶ Tr.obj₃⟦(-1 : ℤ)⟧)) :
    Nonempty (R.obj B ≅ P) := by
  let β : P ⟶ R.obj B := adj.homEquiv _ _ (hι.preimage (e₁.hom ≫ Tr.mor₁ ≫ e₂.inv))
  have hβ : ι.map (L.map β ≫ adj.counit.app B) ≫ e₂.hom = e₁.hom ≫ Tr.mor₁ := by
    have h' : L.map β ≫ adj.counit.app B = hι.preimage (e₁.hom ≫ Tr.mor₁ ≫ e₂.inv) := by
      refine (Adjunction.homEquiv_counit adj _ _ β).symm.trans ?_
      exact (adj.homEquiv _ _).symm_apply_apply _
    rw [h', Functor.FullyFaithful.map_preimage]
    simp
  have := isIso_of_adjunction_triangle_of_fullyFaithful adj hι hL Tr hT e₁ e₂ h₀ h₁ β hβ
  exact ⟨(asIso β).symm⟩

end CategoryTheory.Pretriangulated

namespace CategoryTheory.Adjunction

/-- If `G ⊣ H`, then there are no nonzero maps from an object `A` with `G A = 0` to objects in the
image of `H`. -/
lemma subsingleton_hom_of_isZero {C' D' : Type*} [Category* C'] [Category* D'] {G : C' ⥤ D'}
    {H : D' ⥤ C'} (adj : G ⊣ H) {A : C'} (hA : IsZero (G.obj A)) (W : D') :
    Subsingleton (A ⟶ H.obj W) :=
  ⟨fun _ _ ↦ (adj.homEquiv _ _).symm.injective (hA.eq_of_src _ _)⟩

/-- If `G ⊣ H` and `G` commutes with the shifts, then there are no nonzero maps from an object `A`
with `G A = 0` to the shifts of objects in the image of `H`. -/
lemma subsingleton_hom_shift_of_isZero {C' D' : Type*} [Category* C'] [Category* D']
    [HasShift C' ℤ] [Preadditive D'] [HasShift D' ℤ]
    [∀ n : ℤ, (shiftFunctor D' n).Additive] {G : C' ⥤ D'} {H : D' ⥤ C'} (adj : G ⊣ H)
    [G.CommShift ℤ] {A : C'} (hA : IsZero (G.obj A)) (W : D') (n : ℤ) :
    Subsingleton (A ⟶ (H.obj W)⟦n⟧) := by
  have hz : IsZero (G.obj (A⟦-n⟧)) :=
    ((shiftFunctor D' (-n)).map_isZero hA).of_iso ((G.commShiftIso (-n)).app A)
  have : Subsingleton ((shiftEquiv C' n).symm.functor.obj A ⟶ H.obj W) :=
    ⟨fun _ _ ↦ (adj.homEquiv _ _).symm.injective (hz.eq_of_src _ _)⟩
  exact ((shiftEquiv C' n).symm.toAdjunction.homEquiv _ _).symm.subsingleton

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- Maps from `Rc_* B` to the shifts of `Rj_* W` vanish when the ranges of the open immersion `j`
and of the closed immersion `c` are disjoint: by `Lj^* ⊣ Rj_*` they correspond to maps out of
the shifts of `Lj^* Rc_* B = 0`. -/
lemma subsingleton_hom_rightDerivedLowerStar_shift_of_disjoint
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X U Z : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (c : Z ⟶ X)
    (hjc : Disjoint (Set.range j.base) (Set.range c.base))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)))
    (W : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))) (n : ℤ) :
    Subsingleton ((R((c)_*⟦Λ⟧)).obj B ⟶ (shiftFunctor _ n).obj ((R((j)_*⟦Λ⟧)).obj W)) :=
  (derivedUpperStarLowerStarAdjunction Λ j).subsingleton_hom_shift_of_isZero
    (isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj_of_disjoint Λ j c hjc B) W n

/-- A prime `ℓ` different from the characteristic of a field `F` is invertible on `Spec F`. -/
lemma isUnit_natCast_spec (ℓ : ℕ) [Fact ℓ.Prime] (F : Type u) [Field F]
    [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)] : IsUnit (ℓ : Γ(Spec (.of F), ⊤)) := by
  have hℓF : IsUnit (ℓ : F) := by
    refine IsUnit.mk0 _ fun h ↦ (Fact.out : ringChar F ≠ ℓ) ?_
    exact (Nat.prime_dvd_prime_iff_eq (Fact.out : (ringChar F).Prime) Fact.out).1
      ((ringChar.spec F ℓ).1 h)
  simpa using hℓF.map (ΓSpecIso (.of F)).inv.hom

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

/-- Identify the closed exceptional pullback from a triangle whose third term receives no maps
from closed pushforwards or their shifts. The adjunction and full faithfulness are shared between
the original triangle and its base change. -/
private lemma nonempty_iso_upperShriek_of_distinguished_triangle
    (Tr : Triangle (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology P.left) Ab.{u + 1}) (condensedRingObj 𝐐 P.left))))
    (hT : Tr ∈ distTriang _) (Q : Dᵇc(Z.left)⟦𝐐⟧) (M : Dᵇc(P.left)⟦𝐐⟧)
    (e₁ : ((boundedConstructibleLowerStar ℓ i).obj Q).obj ≅ Tr.obj₁)
    (e₂ : M.obj ≅ Tr.obj₂)
    (h₀ : ∀ B : Dᵇc(Z.left)⟦𝐐⟧,
      Subsingleton (((boundedConstructibleLowerStar ℓ i).obj B).obj ⟶ Tr.obj₃))
    (h₁ : ∀ B : Dᵇc(Z.left)⟦𝐐⟧,
      Subsingleton (((boundedConstructibleLowerStar ℓ i).obj B).obj ⟶ Tr.obj₃⟦(-1 : ℤ)⟧)) :
    Nonempty ((boundedConstructibleUpperShriek ℓ i).obj M ≅ Q) := by
  have hLi : (boundedConstructibleLowerStar ℓ i ⋙ (boundedConstructible _).ι).FullyFaithful :=
    ((ObjectProperty.fullyFaithfulι _).comp
      (derivedUpperStarLowerStarAdjunction 𝐐 i.left).fullyFaithfulROfIsIsoCounit).ofIso
      (boundedConstructibleLowerStarCompatibility ℓ i).symm
  exact nonempty_iso_of_adjunction_triangle
    ((boundedConstructibleUpperShriekAdjunction ℓ i).ofNatIsoLeft
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i))
    (ObjectProperty.fullyFaithfulι _) hLi Tr hT e₁ e₂ h₀ h₁

/-- **Closed exceptional inverse images commute with base change along field extensions**: for a
closed immersion `i : Z ⟶ P` of separated `F`-schemes of finite type, its base change
`i' : Z' ⟶ P'` along a field extension `F ⟶ L` (`πP : P' ⟶ P`, `πZ : Z' ⟶ Z`) and a bounded
constructible `ℚ̄_ℓ`-complex `M` on `P`, `πZ^* Ri^! M ≅ Ri'^! πP^* M`. -/
theorem nonempty_iso_upperShriek_closedImmersion_of_fieldExtension
    (hP : IsPullback πP P'.hom P.hom (Spec.map (CommRingCat.ofHom (algebraMap F L))))
    (sq : IsPullback πZ i'.left i.left πP) (M : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Nonempty ((boundedConstructibleUpperStarOfMap ℓ (X := Z) (Y := Z') πZ).obj
        ((boundedConstructibleUpperShriek ℓ i).obj M) ≅
      (boundedConstructibleUpperShriek ℓ i').obj
        ((boundedConstructibleUpperStarOfMap ℓ (X := P) (Y := P') πP).obj M)) := by
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
  have hjX : IsZero ((L((V.ι)^*⟦𝐐⟧)).obj X) := by
    refine Triangle.isZero₁_of_isIso₂ _ ((L((V.ι)^*⟦𝐐⟧)).map_distinguished _ hT) ?_
    exact IsIso.of_isIso_fac_right (hh := IsIso.id _) (adjV.left_triangle_components M.obj)
  have hiX : IsIso ((derivedUpperStarLowerStarAdjunction 𝐐 i.left).unit.app X) :=
    isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero _ V.ι i.left hcompl hjX
  have : LocallyOfFiniteType (Over.mk (V.ι ≫ P.hom)).hom :=
    inferInstanceAs (LocallyOfFiniteType (V.ι ≫ P.hom))
  have : QuasiCompact (Over.mk (V.ι ≫ P.hom)).hom :=
    inferInstanceAs (QuasiCompact (V.ι ≫ P.hom))
  have : IsSeparated (Over.mk (V.ι ≫ P.hom)).hom :=
    inferInstanceAs (IsSeparated (V.ι ≫ P.hom))
  have hjM := boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ V.ι M.obj M.property
  have hRj : boundedConstructible _ ((R((V.ι)_*⟦𝐐⟧)).obj ((L((V.ι)^*⟦𝐐⟧)).obj M.obj)) :=
    boundedConstructible_rightDerivedLowerStar_obj ℓ
      (Over.homMk V.ι : Over.mk (V.ι ≫ P.hom) ⟶ P) ⟨_, hjM⟩
  have hX : boundedConstructible _ X :=
    (boundedConstructible _).ext_of_isTriangulatedClosed₁ _ hT M.property hRj
  /- The closed part `Q₀ = Li^* X`, with `Ri_* Q₀ ≅ X`. -/
  let Q₀ : Dᵇc(Z.left)⟦𝐐⟧ :=
    ⟨(L((i.left)^*⟦𝐐⟧)).obj X,
      boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ i.left X hX⟩
  let e₁ : (boundedConstructible _).ι.obj ((boundedConstructibleLowerStar ℓ i).obj Q₀) ≅ X :=
    (asIso ((derivedUpperStarLowerStarAdjunction 𝐐 i.left).unit.app X)).symm
  /- `Ri^! M ≅ Q₀`. -/
  obtain ⟨φ₁⟩ := nonempty_iso_upperShriek_of_distinguished_triangle ℓ (i := i)
    _ hT Q₀ M e₁ (Iso.refl _)
    (fun Q ↦ adjV.subsingleton_hom_of_isZero
      (isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj_of_disjoint _ V.ι i.left
        hcompl.symm.disjoint Q.obj) _)
    (fun Q ↦ subsingleton_hom_rightDerivedLowerStar_shift_of_disjoint _ V.ι i.left
        hcompl.symm.disjoint Q.obj _ _)
  /- The pulled back triangle. -/
  let Tr' := (L((πP)^*⟦𝐐⟧)).mapTriangle.obj (Triangle.mk f (adjV.unit.app M.obj) h)
  have hT' : Tr' ∈ distTriang _ := (L((πP)^*⟦𝐐⟧)).map_distinguished _ hT
  have hbcZ : IsIso ((baseChangeMap 𝐐 sq.toCommSq).app Q₀.obj) :=
    have : IsNoetherian P.left := isNoetherian_of_locallyOfFiniteType P.hom
    have : IsNoetherian P'.left := isNoetherian_of_locallyOfFiniteType P'.hom
    isIso_baseChangeMap_app_padicAlgCl_of_isProper ℓ P.hom P'.hom sq.toCommSq sq Q₀.obj
      Q₀.property
  let Q₀' := (boundedConstructibleUpperStarOfMap ℓ (X := Z) (Y := Z') πZ).obj Q₀
  let e₁' : (boundedConstructible _).ι.obj ((boundedConstructibleLowerStar ℓ i').obj Q₀') ≅
      Tr'.obj₁ :=
    (asIso ((baseChangeMap 𝐐 sq.toCommSq).app Q₀.obj)).symm ≪≫ (L((πP)^*⟦𝐐⟧)).mapIso e₁
  have : IsLocallyNoetherian P.left := LocallyOfFiniteType.isLocallyNoetherian P.hom
  have : IsNoetherian V.toScheme := {}
  have hbcU : IsIso ((baseChangeMap 𝐐 sqV.toCommSq).app ((L((V.ι)^*⟦𝐐⟧)).obj M.obj)) := by
    exact_mod_proofs isIso_baseChangeMap_app_padicAlgCl_of_fieldExtension P.hom P'.hom hP ℓ sqV
      (isUnit_natCast_spec ℓ F) _ hjM
  let e₃ : Tr'.obj₃ ≅ (R((V'.ι)_*⟦𝐐⟧)).obj
      ((L((πP ∣_ V)^*⟦𝐐⟧)).obj ((L((V.ι)^*⟦𝐐⟧)).obj M.obj)) :=
    asIso ((baseChangeMap 𝐐 sqV.toCommSq).app ((L((V.ι)^*⟦𝐐⟧)).obj M.obj))
  /- `Ri'^! πP^* M ≅ πZ^* Q₀`. -/
  obtain ⟨φ₂⟩ := nonempty_iso_upperShriek_of_distinguished_triangle ℓ (i := i')
    Tr' hT' Q₀' ((boundedConstructibleUpperStarOfMap ℓ (X := P) (Y := P') πP).obj M)
    e₁' (Iso.refl _)
    (fun Q ↦ @Equiv.subsingleton _ _ (Iso.homCongr (Iso.refl _) e₃)
      ((derivedUpperStarLowerStarAdjunction 𝐐 V'.ι).subsingleton_hom_of_isZero
        (isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj_of_disjoint _ V'.ι i'.left
          hV' Q.obj) _))
    (fun Q ↦ @Equiv.subsingleton _ _
      (Iso.homCongr (Iso.refl _) ((shiftFunctor _ (-1 : ℤ)).mapIso e₃))
      (subsingleton_hom_rightDerivedLowerStar_shift_of_disjoint _ V'.ι i'.left hV' Q.obj _ _))
  exact ⟨(boundedConstructibleUpperStarOfMap ℓ (X := Z) (Y := Z') πZ).mapIso φ₁ ≪≫ φ₂.symm⟩

end AlgebraicGeometry.ProEtale.CondensedRing
