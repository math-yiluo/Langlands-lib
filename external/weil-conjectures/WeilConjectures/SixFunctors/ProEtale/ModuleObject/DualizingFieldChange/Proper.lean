/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Closed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Iso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedUpperShriekFieldExtension
public import WeilConjectures.SmoothPurity.Defs
public import WeilConjectures.TateTwist.Pullback
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Differentials
public import WeilConjectures.TraceFormula.PurityBaseChangeRestriction
public import WeilConjectures.AlgebraicGeometry.ChowLemma

/-!

# Base change of dualizing complexes of proper schemes along field extensions

Let `L/F` be a field extension, `X` a proper `F`-scheme, `X'` its base change to `L` and
`φ_X : π^* ω_X ⟶ ω_{X'}` the comparison of the dualizing complexes
(`ProEtale.CondensedRing.dualizingComplexBaseChange`, for an isomorphism `e : πₛ^* ℚ̄_ℓ ⟶ ℚ̄_ℓ`).
This file proves that `φ_X` is an isomorphism
(`ProEtale.CondensedRing.isIso_dualizingComplexBaseChange_of_fieldExtension`), extending the
projective case of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Smooth`.

## Proof

By noetherian induction on the closed subschemes of `X`
(`ProEtale.CondensedRing.isIso_dualizingComplexBaseChange_of_forall_isClosedImmersion`). Let
`h : Y ⟶ X` be a Chow modification: `Y` is closed in a projective space, hence `φ_Y` is invertible
(`ProEtale.CondensedRing.isIso_dualizingComplexBaseChange_of_isClosedImmersion_projectiveSpace`),
and `h` is an isomorphism over a dense open `U` of `X`, with closed complement `i : Z ⟶ X`.

* *The open part.* By the composition law
  `ProEtale.CondensedRing.dualizingComplexBaseChange_eq_comp_upperShriekBaseChangeOfMap`,
  `φ_Y` is `γ(ω_X) ≫ Rh'^!(φ_X)` up to isomorphisms, `γ` the base change map of `Rh^!`. Over the
  preimage of `U` the base change map is invertible
  (`ProEtale.CondensedRing.isIso_upperStarOfMap_map_upperShriekBaseChangeOfMap_app`): by its counit
  property this reduces to the invertibility of the counit of `Rh_* ⊣ Rh^!` over `U`
  (`ProEtale.CondensedRing.isIso_upperStar_map_lowerStarUpperShriekAdjunction_counit_app`, from
  the exceptional base change along the open immersion `U ⟶ X`) and to proper base change. Hence
  the restriction of `φ_X` to the preimage `U'` of `U` is invertible
  (`ProEtale.CondensedRing.isIso_upperStar_map_dualizingComplexBaseChange_of_isIso`).
* *The closed part.* `φ_Z` is invertible by induction, hence so is `Ri'^! φ_X`
  (`ProEtale.CondensedRing.isIso_dualizingComplexBaseChange_iff_of_isClosedImmersion`).
* *Dévissage.* A morphism `φ` of bounded constructible complexes with `Lj'^* φ` and `Ri'^! φ`
  invertible is invertible
  (`ProEtale.CondensedRing.isIso_of_isIso_upperStar_map_of_isIso_upperShriek_map`): a complex
  `A` with `Lj'^* A = 0` is `Ri'_* Li'^* A`, so that composition with `φ` is bijective on maps out
  of `A`; apply this to the fibre of `φ` and its shift.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C}

/-- For an adjunction `L ⊣ R` and `φ : K ⟶ K'` with `R φ` invertible, composition with `φ` is a
bijection `(L Q ⟶ K) ≃ (L Q ⟶ K')`. -/
lemma bijective_comp_of_isIso_map (adj : L ⊣ R) {K K' : D} (φ : K ⟶ K') [IsIso (R.map φ)]
    (Q : C) : Function.Bijective (fun a : L.obj Q ⟶ K ↦ a ≫ φ) := by
  have h : (fun a : L.obj Q ⟶ K ↦ a ≫ φ) = (adj.homEquiv Q K').symm ∘
      (fun b : Q ⟶ R.obj K ↦ b ≫ R.map φ) ∘ adj.homEquiv Q K := by
    funext a
    simp [homEquiv_naturality_right_symm]
  rw [h]
  refine (adj.homEquiv Q K').symm.bijective.comp ((Function.Bijective.comp ?_
    (adj.homEquiv Q K).bijective))
  refine ⟨fun a b hab ↦ ?_, fun c ↦ ⟨c ≫ inv (R.map φ), by simp⟩⟩
  simpa using congrArg (· ≫ inv (R.map φ)) hab

/-- The counit of an adjunction whose left adjoint is isomorphic to the identity is an
isomorphism. -/
lemma isIso_counit_app_of_leftAdjoint_iso_id {L R : C ⥤ C} (adj : L ⊣ R) (e : L ≅ 𝟭 C) (Y : C) :
    IsIso (adj.counit.app Y) := by
  let adj' := adj.ofNatIsoLeft e
  have : IsIso (adj'.unit.app Y) := by
    have : (𝟭 C).Full := inferInstance
    have : (𝟭 C).Faithful := inferInstance
    infer_instance
  have h : adj'.unit.app Y ≫ adj'.counit.app Y = 𝟙 _ := adj'.left_triangle_components Y
  have h' : adj'.counit.app Y = e.inv.app _ ≫ adj.counit.app Y := by
    simp [adj', ofNatIsoLeft]
  have : IsIso (adj'.counit.app Y) := IsIso.of_isIso_fac_left h
  rw [h'] at this
  exact IsIso.of_isIso_comp_left (e.inv.app _) _

end CategoryTheory.Adjunction

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]

/-- Bijectivity of the composition with `φ` is invariant under isomorphisms of the source. -/
lemma bijective_comp_iff_of_iso {A A' K K' : C} (e : A ≅ A') (φ : K ⟶ K') :
    Function.Bijective (fun a : A ⟶ K ↦ a ≫ φ) ↔
      Function.Bijective (fun a : A' ⟶ K ↦ a ≫ φ) := by
  have h : (fun a : A ⟶ K ↦ a ≫ φ) = (e.homCongr (Iso.refl K')).symm ∘
      (fun a : A' ⟶ K ↦ a ≫ φ) ∘ e.homCongr (Iso.refl K) := by
    funext a
    simp [Iso.homCongr]
  rw [h]
  constructor
  · intro hb
    have := ((e.homCongr (Iso.refl K')).bijective.comp hb).comp
      (e.homCongr (Iso.refl K)).symm.bijective
    convert this using 1
    funext a
    simp
  · intro hb
    exact (e.homCongr (Iso.refl K')).symm.bijective.comp (hb.comp
      (e.homCongr (Iso.refl K)).bijective)

/-- Bijectivity of the composition with `φ` is reflected by fully faithful functors. -/
lemma Functor.FullyFaithful.bijective_comp_map_iff {F : C ⥤ D} (hF : F.FullyFaithful)
    {A K K' : C} (φ : K ⟶ K') :
    Function.Bijective (fun a : F.obj A ⟶ F.obj K ↦ a ≫ F.map φ) ↔
      Function.Bijective (fun a : A ⟶ K ↦ a ≫ φ) := by
  have h : (fun a : F.obj A ⟶ F.obj K ↦ a ≫ F.map φ) = hF.homEquiv ∘
      (fun a : A ⟶ K ↦ a ≫ φ) ∘ hF.homEquiv.symm := by
    funext a
    change _ = F.map (hF.preimage a ≫ φ)
    simp
  rw [h]
  constructor
  · intro hb
    have := (hF.homEquiv.symm.bijective.comp hb).comp hF.homEquiv.bijective
    convert this using 1
    funext a
    simp
  · intro hb
    exact hF.homEquiv.bijective.comp (hb.comp hF.homEquiv.symm.bijective)

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Open–closed detection with the exceptional inverse image -/

section Devissage

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

set_option hygiene false in
/-- The coefficient ring `ℚ̲̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj.{u} ℓ

variable {Z U X : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (i : Z ⟶ X) [IsClosedImmersion i.left] (j : U ⟶ X) [IsOpenImmersion j.left] [QuasiCompact j.left]

omit [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] in
/-- A bounded constructible complex `A` on `X` with `Lj^* A = 0` is of the form `Ri_* Q`, so that
for `φ : K ⟶ K'` with `Ri^! φ` invertible, composition with `φ` is a bijection
`(A ⟶ K) ≃ (A ⟶ K')`. -/
lemma bijective_comp_of_isZero_leftDerivedUpperStar
    (hij : IsCompl (Set.range i.left.base) (Set.range j.left.base))
    {K K' : Dᵇc(X.left)⟦𝐐⟧} (φ : K ⟶ K')
    (hi : IsIso ((boundedConstructibleUpperShriek ℓ i).map φ)) {A : _}
    (hA : boundedConstructible _ A) (hA₀ : IsZero ((L((j.left)^*⟦𝐐⟧)).obj A)) :
    Function.Bijective (fun a : A ⟶ K.obj ↦ a ≫ φ.hom) := by
  have hu := isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero _ j.left i.left hij hA₀
  let Q : Dᵇc(Z.left)⟦𝐐⟧ :=
    ⟨(L((i.left)^*⟦𝐐⟧)).obj A,
      boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ i.left A hA⟩
  let e : (boundedConstructible _).ι.obj ((boundedConstructibleLowerStar ℓ i).obj Q) ≅ A :=
    (asIso ((derivedUpperStarLowerStarAdjunction 𝐐 i.left).unit.app A)).symm
  rw [bijective_comp_iff_of_iso e.symm]
  exact ((ObjectProperty.fullyFaithfulι _).bijective_comp_map_iff φ).2
    ((lowerStarUpperShriekAdjunction ℓ i).bijective_comp_of_isIso_map φ Q)

/-- **Open–closed detection with the exceptional inverse image**: for a quasi-compact open
immersion `j : U ⟶ X` and a closed immersion `i : Z ⟶ X` onto its complement, a morphism `φ`
of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` such that `Lj^* φ` and `Ri^! φ` are isomorphisms is an isomorphism. -/
theorem isIso_of_isIso_upperStar_map_of_isIso_upperShriek_map
    (hij : IsCompl (Set.range i.left.base) (Set.range j.left.base))
    {K K' : Dᵇc(X.left)⟦𝐐⟧} (φ : K ⟶ K')
    (hj : IsIso ((boundedConstructibleUpperStar 𝐐 ℓ j).map φ))
    (hi : IsIso ((boundedConstructibleUpperShriek ℓ i).map φ)) : IsIso φ := by
  have hj' : IsIso ((L((j.left)^*⟦𝐐⟧)).map φ.hom) :=
    (boundedConstructible _).ι.map_isIso ((boundedConstructibleUpperStar 𝐐 ℓ j).map φ)
  obtain ⟨X₀, u, w, hT⟩ := distinguished_cocone_triangle₁ φ.hom
  have hT' := rot_of_distTriang _ hT
  have hX₀ : boundedConstructible _ X₀ :=
    (boundedConstructible _).ext_of_isTriangulatedClosed₁ _ hT K.property K'.property
  have hX₁ : boundedConstructible _ (X₀⟦(1 : ℤ)⟧) :=
    (boundedConstructible _).ext_of_isTriangulatedClosed₃ _ hT' K.property K'.property
  have hjX₀ : IsZero ((L((j.left)^*⟦𝐐⟧)).obj X₀) :=
    Triangle.isZero₁_of_isIso₂ _ ((L((j.left)^*⟦𝐐⟧)).map_distinguished _ hT) hj'
  have hjX₁ : IsZero ((L((j.left)^*⟦𝐐⟧)).obj (X₀⟦(1 : ℤ)⟧)) :=
    Triangle.isZero₃_of_isIso₁ _ ((L((j.left)^*⟦𝐐⟧)).map_distinguished _ hT') hj'
  have hb₀ := bijective_comp_of_isZero_leftDerivedUpperStar ℓ i j hij φ hi hX₀ hjX₀
  have hb₁ := bijective_comp_of_isZero_leftDerivedUpperStar ℓ i j hij φ hi hX₁ hjX₁
  have hu : u = 0 := hb₀.1 (by
    simpa using comp_distTriang_mor_zero₁₂ _ hT)
  have hid : 𝟙 (X₀⟦(1 : ℤ)⟧) = 0 := by
    obtain ⟨s, hs⟩ := Triangle.coyoneda_exact₃ _ hT' (𝟙 _) (by simp [hu])
    obtain ⟨t, rfl⟩ := hb₁.2 s
    have h₂₃ : φ.hom ≫ w = 0 := comp_distTriang_mor_zero₂₃ _ hT
    have hs' : 𝟙 (X₀⟦(1 : ℤ)⟧) = t ≫ φ.hom ≫ w := by
      rw [← Category.assoc]
      exact hs
    rw [h₂₃, Limits.comp_zero] at hs'
    exact hs'
  have hw : w = 0 := by rw [← Category.comp_id w, hid, Limits.comp_zero]
  have hφ : IsIso φ.hom := (Triangle.isZero₁_iff_isIso₂ _ hT).1
    ((Triangle.isZero₁_iff _ hT).2 ⟨hu, hw⟩)
  have : IsIso ((boundedConstructible _).ι.map φ) := hφ
  exact isIso_of_reflects_iso φ (boundedConstructible _).ι

end Devissage

/-! ### The counit of `Rh_* ⊣ Rh^!` over an open where `h` is an isomorphism -/

section OpenCounit

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

set_option hygiene false in
/-- The coefficient ring `ℚ̲̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj.{u} ℓ

variable {Y X U : Over (Spec (.of k))}
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  {h : Y ⟶ X} [IsProper h.left] {j : U ⟶ Y} [IsOpenImmersion j.left]
  [IsOpenImmersion (j ≫ h).left]

/-- **The counit of `Rh_* ⊣ Rh^!` is invertible where `h` is an isomorphism**: for a proper
`h : Y ⟶ X` and an open immersion `j : U ⟶ Y` such that `j ≫ h` is an open immersion and
`U = h⁻¹(U)` (the square `j ≫ h = 𝟙 ≫ (j ≫ h)` is cartesian), the restriction to `U` of the
counit `Rh_* Rh^! M ⟶ M` is an isomorphism. This is read off the exceptional base change map of
the square, which is invertible since `j ≫ h` is an open immersion
(`ProEtale.CondensedRing.isIso_upperStar_map_upperShriekBaseChange_iff_of_isPullback`). -/
theorem isIso_upperStar_map_lowerStarUpperShriekAdjunction_counit_app
    (sq : IsPullback j (𝟙 U) h (j ≫ h)) (M : Dᵇc(X.left)⟦𝐐⟧) :
    IsIso ((boundedConstructibleUpperStar 𝐐 ℓ (j ≫ h)).map
      ((lowerStarUpperShriekAdjunction ℓ h).counit.app M)) := by
  have : Mono j := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))
  have : Mono (j ≫ h) := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono (j ≫ h).left))
  have : IsOpenImmersion (Over.Hom.left (𝟙 U)) := by rw [Over.id_left]; infer_instance
  have sqo : IsPullback (𝟙 U) (𝟙 U) j j := IsKernelPair.id_of_mono j
  have sqU : IsPullback (𝟙 U) (𝟙 U) (j ≫ h) (j ≫ h) := IsKernelPair.id_of_mono _
  have hβ := (isIso_upperStar_map_upperShriekBaseChange_iff_of_isPullback ℓ sq sqo sqU
    (Category.comp_id _) M).2 (isIso_upperShriekBaseChange_of_isOpenImmersion ℓ sqU M)
  rw [NatIso.isIso_map_iff (boundedConstructibleUpperStarId 𝐐 ℓ U)] at hβ
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
  have := (boundedConstructibleUpperShriekAdjunction ℓ (𝟙 U)).isIso_counit_app_of_leftAdjoint_iso_id
    (boundedConstructibleLowerShriekId ℓ U)
    ((boundedConstructibleUpperStar 𝐐 ℓ (j ≫ h)).obj M)
  have hβ' : IsIso (upperShriekBaseChange ℓ sq M) := hβ
  have hx : IsIso (inv ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app
        ((boundedConstructibleUpperShriek ℓ h).obj M)) ≫
      (boundedConstructibleUpperStar 𝐐 ℓ (j ≫ h)).map
        ((boundedConstructibleUpperShriekAdjunction ℓ h).counit.app M)) := by
    have e : inv ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app
          ((boundedConstructibleUpperShriek ℓ h).obj M)) ≫
        (boundedConstructibleUpperStar 𝐐 ℓ (j ≫ h)).map
          ((boundedConstructibleUpperShriekAdjunction ℓ h).counit.app M) =
        (boundedConstructibleLowerShriek ℓ (𝟙 U)).map (upperShriekBaseChange ℓ sq M) ≫
          (boundedConstructibleUpperShriekAdjunction ℓ (𝟙 U)).counit.app
            ((boundedConstructibleUpperStar 𝐐 ℓ (j ≫ h)).obj M) := by
      rw [← Adjunction.homEquiv_counit (boundedConstructibleUpperShriekAdjunction ℓ (𝟙 U))
        (g := upperShriekBaseChange ℓ sq M)]
      exact (((boundedConstructibleUpperShriekAdjunction ℓ (𝟙 U)).homEquiv _ _).symm_apply_apply
        _).symm
    rw [e]
    infer_instance
  have h₁ := IsIso.of_isIso_comp_left
    (inv ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app
      ((boundedConstructibleUpperShriek ℓ h).obj M)))
    ((boundedConstructibleUpperStar 𝐐 ℓ (j ≫ h)).map
      ((boundedConstructibleUpperShriekAdjunction ℓ h).counit.app M))
  have hc : (lowerStarUpperShriekAdjunction ℓ h).counit.app M =
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ h).inv.app _ ≫
        (boundedConstructibleUpperShriekAdjunction ℓ h).counit.app M := by
    simp [lowerStarUpperShriekAdjunction]
  rw [hc, Functor.map_comp]
  infer_instance

end OpenCounit

/-! ### Restriction of the comparison to an open where a modification is an isomorphism -/

section OpenRestriction

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)]

set_option hygiene false in
/-- The coefficient ring `ℚ̲̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj.{u} ℓ

omit [Fact (ringChar k₁).Prime] [Fact (ringChar k₂).Prime] [Fact (ringChar k₁ ≠ ℓ)]
  [Fact (ringChar k₂ ≠ ℓ)] in
/-- If `Lo^* f` is invertible, so is `Lo'^* Lπ^* f`, for a commutative square
`πU ≫ o = o' ≫ π`. -/
lemma isIso_upperStarOfMap_map_upperStarOfMap_map {X U : Over (Spec (.of k₁))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    {X' U' : Over (Spec (.of k₂))}
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
    {o : U.left ⟶ X.left} {o' : U'.left ⟶ X'.left} {π : X'.left ⟶ X.left}
    {πU : U'.left ⟶ U.left} (w : πU ≫ o = o' ≫ π) {A B : Dᵇc(X.left)⟦𝐐⟧} (f : A ⟶ B)
    (hf : IsIso ((boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := U) o).map f)) :
    IsIso ((boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := U') o').map
      ((boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') π).map f)) := by
  have hf' : IsIso ((L((o)^*⟦𝐐⟧)).map f.hom) :=
    (boundedConstructible _).ι.map_isIso ((boundedConstructibleUpperStarOfMap ℓ o).map f)
  have h₁ : IsIso ((L((πU ≫ o)^*⟦𝐐⟧)).map f.hom) := by
    rw [NatIso.isIso_map_iff (leftDerivedUpperStarComp 𝐐 πU o)]
    exact (inferInstance : IsIso ((L((πU)^*⟦𝐐⟧)).map ((L((o)^*⟦𝐐⟧)).map f.hom)))
  rw [w, NatIso.isIso_map_iff (leftDerivedUpperStarComp 𝐐 o' π)] at h₁
  have : IsIso ((boundedConstructible _).ι.map ((boundedConstructibleUpperStarOfMap ℓ o').map
      ((boundedConstructibleUpperStarOfMap ℓ π).map f))) := h₁
  exact isIso_of_reflects_iso _ (boundedConstructible _).ι

variable {Y X U : Over (Spec (.of k₁))}
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  {h : Y ⟶ X} [IsProper h.left] {j : U ⟶ Y} [IsOpenImmersion j.left]
  [IsOpenImmersion (j ≫ h).left]
  {Y' X' U' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
  {h' : Y' ⟶ X'} [IsProper h'.left] {j' : U' ⟶ Y'} [IsOpenImmersion j'.left]
  [IsOpenImmersion (j' ≫ h').left]
  {πY : Y'.left ⟶ Y.left} {πX : X'.left ⟶ X.left} {πU : U'.left ⟶ U.left}

/-- **The base change map of `Rh^!` is invertible where `h` is an isomorphism**: let
`h : Y ⟶ X` be proper and `j : U ⟶ Y` an open immersion with `U = h⁻¹(U)` and `j ≫ h` an open
immersion, and similarly over a second field, with a cartesian square `πY ≫ h = h' ≫ πX` and a
commutative square `πU ≫ (j ≫ h) = (j' ≫ h') ≫ πX`. Then the restriction to `U'` of the base change
map `πY^* Rh^! M ⟶ Rh'^! πX^* M` (`ProEtale.CondensedRing.upperShriekBaseChangeOfMap`) is an
isomorphism. Indeed, by the counit property of the base change map and
`ProEtale.CondensedRing.isIso_upperStar_map_lowerStarUpperShriekAdjunction_counit_app` its image
under `Rh'_*` is invertible over `U'`, and `Rh'_*` restricted to `U'` is the restriction to `U'`
of `Y'` (proper base change). -/
theorem isIso_upperStarOfMap_map_upperShriekBaseChangeOfMap_app
    (sq : IsPullback j (𝟙 U) h (j ≫ h)) (sq' : IsPullback j' (𝟙 U') h' (j' ≫ h'))
    (sqf : IsPullback πY h'.left h.left πX) (w : πU ≫ (j ≫ h).left = (j' ≫ h').left ≫ πX)
    (M : Dᵇc(X.left)⟦𝐐⟧) :
    IsIso ((boundedConstructibleUpperStarOfMap ℓ (X := Y') (Y := U') j'.left).map
      ((upperShriekBaseChangeOfMap ℓ sqf).app M)) := by
  have := isIso_boundedConstructibleBaseChangeOfMap ℓ sqf
  have hc := lowerStar_map_upperShriekBaseChangeOfMap_app_comp_counit ℓ sqf M
  /- The restriction of the counits to `U` and `U'`. -/
  have hε : IsIso ((boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := U) (j ≫ h).left).map
      ((lowerStarUpperShriekAdjunction ℓ h).counit.app M)) :=
    isIso_upperStar_map_lowerStarUpperShriekAdjunction_counit_app ℓ sq M
  have hε' : IsIso ((boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := U') (j' ≫ h').left).map
      ((lowerStarUpperShriekAdjunction ℓ h').counit.app
        ((boundedConstructibleUpperStarOfMap ℓ πX).obj M))) :=
    isIso_upperStar_map_lowerStarUpperShriekAdjunction_counit_app ℓ sq' _
  have hπε := isIso_upperStarOfMap_map_upperStarOfMap_map ℓ w _ hε
  /- The restriction of `Rh'_*` of the base change map to `U'` is invertible. -/
  have h₁ : IsIso ((boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := U') (j' ≫ h').left).map
      ((boundedConstructibleLowerStar ℓ h').map ((upperShriekBaseChangeOfMap ℓ sqf).app M))) := by
    have h₂ := congrArg
      (boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := U') (j' ≫ h').left).map hc
    simp only [Functor.map_comp] at h₂
    have : IsIso ((boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := U') (j' ≫ h').left).map
        ((boundedConstructibleLowerStar ℓ h').map ((upperShriekBaseChangeOfMap ℓ sqf).app M)) ≫
      (boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := U') (j' ≫ h').left).map
        ((lowerStarUpperShriekAdjunction ℓ h').counit.app
          ((boundedConstructibleUpperStarOfMap ℓ πX).obj M))) := by
      rw [h₂]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := U') (j' ≫ h').left).map
        ((lowerStarUpperShriekAdjunction ℓ h').counit.app
          ((boundedConstructibleUpperStarOfMap ℓ πX).obj M)))
  /- Proper base change along the open immersion `j' ≫ h'`. -/
  have sq₂ : IsPullback j'.left (Over.Hom.left (𝟙 U')) h'.left (j' ≫ h').left := by
    simpa using sq'.map (Over.forget _)
  have := isIso_boundedConstructibleBaseChangeOfMap ℓ sq₂
  have hn := (boundedConstructibleBaseChangeOfMap ℓ sq₂.toCommSq).naturality
    ((upperShriekBaseChangeOfMap ℓ sqf).app M)
  have h₃ : IsIso ((boundedConstructibleLowerStar ℓ (𝟙 U')).map
      ((boundedConstructibleUpperStarOfMap ℓ (X := Y') (Y := U') j'.left).map
        ((upperShriekBaseChangeOfMap ℓ sqf).app M))) := by
    have : IsIso ((boundedConstructibleBaseChangeOfMap ℓ sq₂.toCommSq).app _ ≫
        (boundedConstructibleLowerStar ℓ (𝟙 U')).map
          ((boundedConstructibleUpperStarOfMap ℓ (X := Y') (Y := U') j'.left).map
            ((upperShriekBaseChangeOfMap ℓ sqf).app M))) := by
      simp only [Functor.comp_map] at hn
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_left ((boundedConstructibleBaseChangeOfMap ℓ sq₂.toCommSq).app _) _
  rwa [NatIso.isIso_map_iff (boundedConstructibleLowerStarId ℓ U')] at h₃

/-- **The comparison of dualizing complexes over an open where a modification is an isomorphism**:
in the situation of `isIso_upperStarOfMap_map_upperShriekBaseChangeOfMap_app`, for proper
`k₁`-schemes `X`, `Y` and their base changes `X'`, `Y'` along `πₛ`, if the comparison `φ_Y` of the
dualizing complexes of `Y` is an isomorphism, then so is the restriction of `φ_X` to the open
`U'` of `X'`. Indeed `φ_Y = πY^*(ρ⁻¹) ≫ γ(ω_X) ≫ Rh'^!(φ_X) ≫ ρ'`
(`ProEtale.CondensedRing.dualizingComplexBaseChange_eq_comp_upperShriekBaseChangeOfMap`), the base
change map `γ` is invertible over `U'`, and `j'^* Rh'^! ≅ R(j' ≫ h')^! ≅ (j' ≫ h')^*`. -/
theorem isIso_upperStar_map_dualizingComplexBaseChange_of_isIso [IsProper (toPoint X).left]
    [IsProper (toPoint Y).left] [IsProper (toPoint X').left] [IsProper (toPoint Y').left]
    {πₛ : Spec (.of k₂) ⟶ Spec (.of k₁)}
    (e : (boundedConstructibleUpperStarOfMap ℓ (X := point k₁) (Y := point k₂) πₛ).obj (𝟙_ _) ⟶
      𝟙_ _)
    (sqX : IsPullback πX (toPoint X').left (toPoint X).left πₛ)
    (sqY : IsPullback πY (toPoint Y').left (toPoint Y).left πₛ)
    (sq : IsPullback j (𝟙 U) h (j ≫ h)) (sq' : IsPullback j' (𝟙 U') h' (j' ≫ h'))
    (sqf : IsPullback πY h'.left h.left πX) (w : πU ≫ (j ≫ h).left = (j' ≫ h').left ≫ πX)
    [IsIso (dualizingComplexBaseChange ℓ e sqY)] :
    IsIso ((boundedConstructibleUpperStar 𝐐 ℓ (j' ≫ h')).map
      (dualizingComplexBaseChange ℓ e sqX)) := by
  have hY := dualizingComplexBaseChange_eq_comp_upperShriekBaseChangeOfMap ℓ e sqX sqY sqf
  have h₁ : IsIso ((upperShriekBaseChangeOfMap ℓ sqf).app (dualizingComplex ℓ X) ≫
      (boundedConstructibleUpperShriek ℓ h').map (dualizingComplexBaseChange ℓ e sqX)) := by
    have h₀ : IsIso ((boundedConstructibleUpperStarOfMap ℓ πY).map
        (upperShriekDualizingComplexIso ℓ h).inv ≫
        (upperShriekBaseChangeOfMap ℓ sqf).app (dualizingComplex ℓ X) ≫
          (boundedConstructibleUpperShriek ℓ h').map (dualizingComplexBaseChange ℓ e sqX) ≫
        (upperShriekDualizingComplexIso ℓ h').hom) := by
      rw [← hY]
      infer_instance
    have h₀' := IsIso.of_isIso_comp_left ((boundedConstructibleUpperStarOfMap ℓ πY).map
      (upperShriekDualizingComplexIso ℓ h).inv) ((upperShriekBaseChangeOfMap ℓ sqf).app
        (dualizingComplex ℓ X) ≫ (boundedConstructibleUpperShriek ℓ h').map
          (dualizingComplexBaseChange ℓ e sqX) ≫ (upperShriekDualizingComplexIso ℓ h').hom)
    rw [← Category.assoc] at h₀'
    exact IsIso.of_isIso_comp_right _ (upperShriekDualizingComplexIso ℓ h').hom
  have h₂ := isIso_upperStarOfMap_map_upperShriekBaseChangeOfMap_app ℓ sq sq' sqf w
    (dualizingComplex ℓ X)
  have h₃ : IsIso ((boundedConstructibleUpperStarOfMap ℓ (X := Y') (Y := U') j'.left).map
      ((boundedConstructibleUpperShriek ℓ h').map (dualizingComplexBaseChange ℓ e sqX))) := by
    have h₄ : IsIso ((boundedConstructibleUpperStarOfMap ℓ (X := Y') (Y := U') j'.left).map
        ((upperShriekBaseChangeOfMap ℓ sqf).app (dualizingComplex ℓ X) ≫
          (boundedConstructibleUpperShriek ℓ h').map (dualizingComplexBaseChange ℓ e sqX))) :=
      inferInstance
    rw [Functor.map_comp] at h₄
    exact IsIso.of_isIso_comp_left ((boundedConstructibleUpperStarOfMap ℓ (X := Y') (Y := U')
      j'.left).map ((upperShriekBaseChangeOfMap ℓ sqf).app (dualizingComplex ℓ X))) _
  replace h₃ : IsIso ((boundedConstructibleUpperStar 𝐐 ℓ j').map
      ((boundedConstructibleUpperShriek ℓ h').map (dualizingComplexBaseChange ℓ e sqX))) := h₃
  rw [← NatIso.isIso_map_iff (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j'),
    ← Functor.comp_map,
    ← NatIso.isIso_map_iff (boundedConstructibleUpperShriekComp_padicAlgCl ℓ j' h'),
    NatIso.isIso_map_iff (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ (j' ≫ h'))]
    at h₃
  exact h₃

end OpenRestriction

/-! ### Closed subschemes of projective spaces

The statements of this section are those of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Smooth`, for a projective
space with an arbitrary finite nonempty set of homogeneous coordinates. -/

section Projective

variable (ℓ : ℕ) [Fact ℓ.Prime] {F L : Type u} [Field F] [Field L] [Algebra F L]
  [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)] [Fact (ringChar L).Prime]
  [Fact (ringChar L ≠ ℓ)]

/-- The pullback of the shifted Tate twists across fields,
`πP^* ℚ̄_ℓ(d)[n] ≅ ℚ̄_ℓ(d)[n]` (as
`ProEtale.CondensedRing.boundedConstructibleUpperStarOfMapTateTwistIso`). -/
private noncomputable def upperStarOfMapTateTwistIso {P : Over (Spec (.of F))}
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    {P' : Over (Spec (.of L))} [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom]
    [IsSeparated P'.hom] (πP : P'.left ⟶ P.left) (d n : ℤ) :
    (boundedConstructibleUpperStarOfMap ℓ (X := P) (Y := P') πP).obj
        (boundedConstructibleTateTwist ℓ P d n) ≅
      boundedConstructibleTateTwist ℓ P' d n :=
  have : NeZero (ℓ : F) := CondensedRing.neZero_natCast_of_ringChar_ne ℓ
  have := QuasiCompact.compactSpace_of_compactSpace P.hom
  have := QuasiCompact.compactSpace_of_compactSpace P'.hom
  have := quasiSeparatedSpace_of_quasiSeparated P.hom
  have := quasiSeparatedSpace_of_quasiSeparated P'.hom
  (ObjectProperty.fullyFaithfulι _).preimageIso
    (((πP)^*⟦Profinite.padicAlgClRingObj ℓ⟧.leftDerivedFunctor.commShiftIso n).app _ ≪≫
      (shiftFunctor _ n).mapIso
        (ProEtale.upperStarTateTwistDerivedIso ℓ πP P.hom d))

/-- **Base change of dualizing complexes along a field extension, embedded case**: for a proper
`F`-scheme `X` with a closed immersion into an `F`-scheme `P` smooth of pure relative dimension
`d`, and its base change along a field extension `L/F`, the comparison
`φ : π^* ω_X ⟶ ω_{X'}` of the dualizing complexes is an isomorphism (as
`ProEtale.CondensedRing.isIso_dualizingComplexBaseChange_of_isClosedImmersion_of_smooth`). -/
private theorem isIso_dualizingComplexBaseChange_of_isClosedImmersion_of_smooth'
    {X P : Over (Spec (.of F))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    {X' P' : Over (Spec (.of L))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
    {i : X ⟶ P} {i' : X' ⟶ P'} [IsClosedImmersion i.left] [IsClosedImmersion i'.left]
    {πP : P'.left ⟶ P.left} {π : X'.left ⟶ X.left}
    [IsProper (toPoint X).left] [IsProper (toPoint X').left]
    (e : (boundedConstructibleUpperStarOfMap ℓ (X := point F) (Y := point L)
      (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj (𝟙_ _) ⟶ 𝟙_ _) [IsIso e]
    (sqX : IsPullback π (toPoint X').left (toPoint X).left
      (Spec.map (CommRingCat.ofHom (algebraMap F L))))
    (d : ℕ) [SmoothOfRelativeDimension d (toPoint P).left]
    [SmoothOfRelativeDimension d (toPoint P').left]
    (hP : IsPullback πP P'.hom P.hom (Spec.map (CommRingCat.ofHom (algebraMap F L))))
    (sq : IsPullback π i'.left i.left πP) :
    IsIso (dualizingComplexBaseChange ℓ e sqX) := by
  obtain ⟨β⟩ := nonempty_iso_upperShriek_closedImmersion_of_fieldExtension ℓ hP sq
    (boundedConstructibleTateTwist ℓ P d (2 * d))
  have ωP : boundedConstructibleTateTwist ℓ P d (2 * d) ≅ dualizingComplex ℓ P :=
    asIso (smoothPurityMap ℓ (toPoint P) d)
  have ωP' : boundedConstructibleTateTwist ℓ P' d (2 * d) ≅ dualizingComplex ℓ P' :=
    asIso (smoothPurityMap ℓ (toPoint P') d)
  exact isIso_dualizingComplexBaseChange_of_iso ℓ e sqX
    ((boundedConstructibleUpperStarOfMap ℓ π).mapIso
      ((upperShriekDualizingComplexIso ℓ i).symm ≪≫
        (boundedConstructibleUpperShriek ℓ i).mapIso ωP.symm) ≪≫ β ≪≫
    (boundedConstructibleUpperShriek ℓ i').mapIso
      (upperStarOfMapTateTwistIso ℓ πP d (2 * d) ≪≫ ωP') ≪≫
    upperShriekDualizingComplexIso ℓ i')

variable {X : Over (Spec (.of F))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] {X' : Over (Spec (.of L))} [LocallyOfFiniteType X'.hom]
  [QuasiCompact X'.hom] [IsSeparated X'.hom] {π : X'.left ⟶ X.left}

/-- **Base change of dualizing complexes along a field extension, projective case**: for a closed
`F`-subscheme `X` of a projective space `ℙ(N; F)` with `N` finite nonempty and its base change
`X'` along a field extension `L/F`, the comparison `φ : π^* ω_X ⟶ ω_{X'}` of the dualizing
complexes is an isomorphism. -/
theorem isIso_dualizingComplexBaseChange_of_isClosedImmersion_projectiveSpace
    [IsProper (toPoint X).left] [IsProper (toPoint X').left]
    (e : (boundedConstructibleUpperStarOfMap ℓ (X := point F) (Y := point L)
      (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj (𝟙_ _) ⟶ 𝟙_ _) [IsIso e]
    (sqX : IsPullback π (toPoint X').left (toPoint X).left
      (Spec.map (CommRingCat.ofHom (algebraMap F L))))
    (N : Type u) (d : ℕ) (hN : Nat.card N = d + 1) (c : X.left ⟶ ℙ(N; Spec (.of F)))
    [IsClosedImmersion c] (hc : c ≫ ℙ(N; Spec (.of F)) ↘ Spec (.of F) = X.hom) :
    IsIso (dualizingComplexBaseChange ℓ e sqX) := by
  have : Finite N := Nat.finite_of_card_ne_zero (by omega)
  let πs := Spec.map (CommRingCat.ofHom (algebraMap F L))
  let P : Over (Spec (.of F)) := Over.mk (ℙ(N; Spec (.of F)) ↘ _)
  let P' : Over (Spec (.of L)) := Over.mk (ℙ(N; Spec (.of L)) ↘ _)
  have : IsProper P.hom := inferInstanceAs (IsProper (ℙ(N; _) ↘ _))
  have : IsProper P'.hom := inferInstanceAs (IsProper (ℙ(N; _) ↘ _))
  let πP : P'.left ⟶ P.left := ProjectiveSpace.map _ πs
  have hP : IsPullback πP P'.hom P.hom πs := ProjectiveSpace.isPullback_map _ πs
  have hX : IsPullback π X'.hom X.hom πs := by simpa using sqX
  let c' : X'.left ⟶ P'.left := hP.lift (π ≫ c) X'.hom (by
    rw [Category.assoc]
    change π ≫ c ≫ P.hom = _
    simp only [P, Over.mk_hom, hc, hX.w])
  have hc'₁ : c' ≫ πP = π ≫ c := hP.lift_fst _ _ _
  have hc'₂ : c' ≫ P'.hom = X'.hom := hP.lift_snd _ _ _
  have sq : IsPullback π c' c πP := by
    refine IsPullback.of_bot ?_ hc'₁.symm hP
    rw [hc'₂]
    exact hc ▸ hX
  have : IsClosedImmersion c' := MorphismProperty.of_isPullback sq inferInstance
  let i : X ⟶ P := Over.homMk c hc
  let i' : X' ⟶ P' := Over.homMk c' hc'₂
  have : IsClosedImmersion i.left := ‹IsClosedImmersion c›
  have : IsClosedImmersion i'.left := ‹IsClosedImmersion c'›
  have : SmoothOfRelativeDimension d (toPoint P).left := by
    rw [toPoint_left]; exact ProjectiveSpace.smoothOfRelativeDimension _ _ hN
  have : SmoothOfRelativeDimension d (toPoint P').left := by
    rw [toPoint_left]; exact ProjectiveSpace.smoothOfRelativeDimension _ _ hN
  exact isIso_dualizingComplexBaseChange_of_isClosedImmersion_of_smooth' ℓ (i := i) (i' := i') e
    sqX d hP sq

end Projective

/-! ### Proper schemes -/

section ProperScheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {F L : Type u} [Field F] [Field L] [Algebra F L]
  [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)] [Fact (ringChar L).Prime]
  [Fact (ringChar L ≠ ℓ)]
  (e : (boundedConstructibleUpperStarOfMap ℓ (X := point F) (Y := point L)
    (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj (𝟙_ _) ⟶ 𝟙_ _) [IsIso e]

/-- **Base change of dualizing complexes of an empty scheme**. -/
theorem isIso_dualizingComplexBaseChange_of_isEmpty {X : Over (Spec (.of F))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [IsProper (toPoint X).left] [IsEmpty X.left] {X' : Over (Spec (.of L))}
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [IsProper (toPoint X').left] {π : X'.left ⟶ X.left}
    (sqX : IsPullback π (toPoint X').left (toPoint X).left
      (Spec.map (CommRingCat.ofHom (algebraMap F L)))) :
    IsIso (dualizingComplexBaseChange ℓ e sqX) :=
  isIso_dualizingComplexBaseChange_of_isClosedImmersion_projectiveSpace ℓ e sqX PUnit 0
    (by simp) (isInitialOfIsEmpty.to _) (isInitialOfIsEmpty.hom_ext _ _)

/-- **The inductive step**: let `X` be a nonempty proper `F`-scheme such that the comparison of
the dualizing complexes is an isomorphism for every closed subscheme `Z ⊊ X` and every base
change of `Z` along `L/F`. Then the comparison `φ_X` is an isomorphism for every base change of
`X` along `L/F`.

Let `h : Y ⟶ X` be a Chow modification (`AlgebraicGeometry.ChowModification`): `Y` is closed in a
projective space, so `φ_Y` is invertible, and `h` is an isomorphism over a dense open `U ⊆ X`.
Hence `φ_X` is invertible over the preimage `U'` of `U`
(`ProEtale.CondensedRing.isIso_upperStar_map_dualizingComplexBaseChange_of_isIso`), and
`Ri'^! φ_X` is invertible for the reduced closed complement `i : Z ⟶ X` of `U` by the induction
hypothesis (`ProEtale.CondensedRing.isIso_dualizingComplexBaseChange_iff_of_isClosedImmersion`).
Thus `φ_X` is invertible
(`ProEtale.CondensedRing.isIso_of_isIso_upperStar_map_of_isIso_upperShriek_map`). -/
theorem isIso_dualizingComplexBaseChange_of_forall_isClosedImmersion
    (X : Over (Spec (.of F))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [IsProper (toPoint X).left]
    (ih : ∀ (Z : Over (Spec (.of F))) [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
      [IsSeparated Z.hom] [IsProper (toPoint Z).left] (i : Z.left ⟶ X.left)
      [IsClosedImmersion i], Set.range i.base ≠ Set.univ →
      ∀ (Z' : Over (Spec (.of L))) [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom]
        [IsSeparated Z'.hom] [IsProper (toPoint Z').left] (πZ : Z'.left ⟶ Z.left)
        (sqZ : IsPullback πZ (toPoint Z').left (toPoint Z).left
          (Spec.map (CommRingCat.ofHom (algebraMap F L)))),
        IsIso (dualizingComplexBaseChange ℓ e sqZ))
    {X' : Over (Spec (.of L))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated X'.hom] [IsProper (toPoint X').left] {π : X'.left ⟶ X.left}
    (sqX : IsPullback π (toPoint X').left (toPoint X).left
      (Spec.map (CommRingCat.ofHom (algebraMap F L)))) :
    IsIso (dualizingComplexBaseChange ℓ e sqX) := by
  let πs := Spec.map (CommRingCat.ofHom (algebraMap F L))
  have hX : IsPullback π X'.hom X.hom πs := by simpa using sqX
  have : IsProper X.hom := by simpa using ‹IsProper (toPoint X).left›
  have : IsProper X'.hom := by simpa using ‹IsProper (toPoint X').left›
  cases isEmpty_or_nonempty X.left with
  | inl _ => exact isIso_dualizingComplexBaseChange_of_isEmpty ℓ e sqX
  | inr hne =>
  /- The Chow modification `h₀ : Y ⟶ X`. -/
  let h₀ := ChowModification.modificationMap X.hom
  let Y : Over (Spec (.of F)) := Over.mk (h₀ ≫ X.hom)
  have : IsProper Y.hom := inferInstanceAs (IsProper (h₀ ≫ X.hom))
  have : IsProper (toPoint Y).left := by rw [toPoint_left]; infer_instance
  let h : Y ⟶ X := Over.homMk h₀ rfl
  have : IsProper h.left := inferInstanceAs (IsProper h₀)
  let Y' : Over (Spec (.of L)) := Over.mk (pullback.snd h₀ π ≫ X'.hom)
  have : IsProper Y'.hom := inferInstanceAs (IsProper (pullback.snd h₀ π ≫ X'.hom))
  have : IsProper (toPoint Y').left := by rw [toPoint_left]; infer_instance
  let h' : Y' ⟶ X' := Over.homMk (pullback.snd h₀ π) rfl
  have : IsProper h'.left := inferInstanceAs (IsProper (pullback.snd h₀ π))
  let πY : Y'.left ⟶ Y.left := pullback.fst h₀ π
  have sqf : IsPullback πY h'.left h.left π := IsPullback.of_hasPullback h₀ π
  have sqY : IsPullback πY (toPoint Y').left (toPoint Y).left πs := by
    simpa [Y, Y'] using sqf.paste_vert hX
  /- The comparison for `Y` is an isomorphism (projective case). -/
  have hφY : IsIso (dualizingComplexBaseChange ℓ e sqY) := by
    obtain ⟨y, -⟩ := h₀.surjective hne.some
    let c := ChowModification.toProjectiveSpace X.hom
    have hy : c y ∈ (⊤ : (ℙ(ChowModification.index X.hom; Spec (.of F))).Opens) := trivial
    rw [← ProjectiveSpace.iSup_standardOpen, TopologicalSpace.Opens.mem_iSup] at hy
    obtain ⟨n, -⟩ := hy
    have : Nonempty (ChowModification.index X.hom) := ⟨n⟩
    have hN : Nat.card (ChowModification.index X.hom) =
        (Nat.card (ChowModification.index X.hom) - 1) + 1 := by
      have := Nat.card_pos (α := ChowModification.index X.hom)
      omega
    exact isIso_dualizingComplexBaseChange_of_isClosedImmersion_projectiveSpace ℓ e sqY _ _ hN c
      (ChowModification.toProjectiveSpace_over X.hom)
  /- The dense open `U` of `X` over which `h` is an isomorphism, its preimage `V` in `Y`. -/
  obtain ⟨U, hUd, hUi⟩ := ChowModification.exists_dense_isIso_restrict X.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsNoetherian Y.left := {}
  let V : Y.left.Opens := h₀ ⁻¹ᵁ U
  have : QuasiCompact V.ι :=
    (quasiCompact_iff_compactSpace _).mpr (isCompact_iff_compactSpace.mp
      (TopologicalSpace.NoetherianSpace.isCompact _))
  let o₀ : V.toScheme ⟶ X.left := V.ι ≫ h₀
  have ho₀ : o₀ = (h₀ ∣_ U) ≫ U.ι := (morphismRestrict_ι h₀ U).symm
  have : IsOpenImmersion o₀ := by rw [ho₀]; infer_instance
  have hro₀ : Set.range o₀ = U := by
    rw [ho₀, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      (h₀ ∣_ U).surjective.range_eq, Set.image_univ, Scheme.Opens.range_ι]
  let Ũ : Over (Spec (.of F)) := Over.mk (V.ι ≫ Y.hom)
  have : LocallyOfFiniteType Ũ.hom := inferInstanceAs (LocallyOfFiniteType (V.ι ≫ Y.hom))
  have : QuasiCompact Ũ.hom := inferInstanceAs (QuasiCompact (V.ι ≫ Y.hom))
  have : IsSeparated Ũ.hom := inferInstanceAs (IsSeparated (V.ι ≫ Y.hom))
  let j : Ũ ⟶ Y := Over.homMk V.ι rfl
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion V.ι)
  have : IsOpenImmersion (j ≫ h).left := inferInstanceAs (IsOpenImmersion o₀)
  have sq₀ : IsPullback V.ι (𝟙 _) h₀ o₀ := by
    have := (IsPullback.of_vert_isIso (fst := 𝟙 V.toScheme) (snd := 𝟙 V.toScheme)
      (f := h₀ ∣_ U) (g := h₀ ∣_ U) ⟨rfl⟩).paste_horiz (isPullback_morphismRestrict h₀ U).flip
    rwa [Category.id_comp, ← ho₀] at this
  have sq : IsPullback j (𝟙 Ũ) h (j ≫ h) :=
    IsPullback.of_map (Over.forget _) (by simp) sq₀
  /- The base change `U'` of `U`. -/
  let Ũ' : Over (Spec (.of L)) := Over.mk (pullback.snd o₀ π ≫ X'.hom)
  have : LocallyOfFiniteType Ũ'.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd o₀ π ≫ X'.hom))
  have : QuasiCompact Ũ'.hom := inferInstanceAs (QuasiCompact (pullback.snd o₀ π ≫ X'.hom))
  have : IsSeparated Ũ'.hom := inferInstanceAs (IsSeparated (pullback.snd o₀ π ≫ X'.hom))
  let πU : Ũ'.left ⟶ Ũ.left := pullback.fst o₀ π
  have hj'w : (pullback.fst o₀ π ≫ V.ι) ≫ h₀ = pullback.snd o₀ π ≫ π := by
    rw [Category.assoc]
    exact pullback.condition
  let j' : Ũ' ⟶ Y' := Over.homMk (sqf.lift (pullback.fst o₀ π ≫ V.ι) (pullback.snd o₀ π) hj'w)
    (by
      change sqf.lift _ _ hj'w ≫ pullback.snd h₀ π ≫ X'.hom = pullback.snd o₀ π ≫ X'.hom
      rw [← Category.assoc]
      exact congrArg (· ≫ X'.hom) (sqf.lift_snd _ _ hj'w))
  have hj'₁ : j'.left ≫ πY = πU ≫ V.ι := sqf.lift_fst _ _ hj'w
  have hj'₂ : j'.left ≫ h'.left = pullback.snd o₀ π := sqf.lift_snd _ _ hj'w
  have : IsOpenImmersion (j' ≫ h').left := by
    rw [Over.comp_left, hj'₂]
    infer_instance
  have sqj' : IsPullback πU j'.left V.ι πY := by
    refine IsPullback.of_bot ?_ hj'₁.symm sqf
    rw [hj'₂]
    exact IsPullback.of_hasPullback o₀ π
  have : IsOpenImmersion j'.left := MorphismProperty.of_isPullback sqj' inferInstance
  have sq'₀ : IsPullback j'.left (𝟙 _) h'.left (j'.left ≫ h'.left) := by
    refine IsPullback.of_right ?_ (by simp) sqf
    rw [hj'₁, hj'₂, ← pullback.condition]
    exact (IsPullback.of_vert_isIso (fst := πU) (snd := 𝟙 _) (f := 𝟙 _) (g := πU)
      ⟨by simp⟩).paste_horiz sq₀
  have sq' : IsPullback j' (𝟙 Ũ') h' (j' ≫ h') :=
    IsPullback.of_map (Over.forget _) (by simp) (by simpa using sq'₀)
  have w : πU ≫ (j ≫ h).left = (j' ≫ h').left ≫ π := by
    change πU ≫ o₀ = (j'.left ≫ h'.left) ≫ π
    rw [hj'₂]
    exact pullback.condition
  have hU := isIso_upperStar_map_dualizingComplexBaseChange_of_isIso ℓ e sqX sqY sq sq' sqf w
  /- The reduced closed complement `Z` of `U` and its base change `Z'`. -/
  let Z₀ : TopologicalSpace.Closeds X.left := ⟨(U : Set X.left)ᶜ, U.isOpen.isClosed_compl⟩
  let i₀ := (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι
  have hri₀ : Set.range i₀ = (U : Set X.left)ᶜ := by simp [i₀, Z₀]
  let Z : Over (Spec (.of F)) := Over.mk (i₀ ≫ X.hom)
  have : IsProper Z.hom := inferInstanceAs (IsProper (i₀ ≫ X.hom))
  have : IsProper (toPoint Z).left := by rw [toPoint_left]; infer_instance
  let Z' : Over (Spec (.of L)) := Over.mk (pullback.snd i₀ π ≫ X'.hom)
  have : IsProper Z'.hom := inferInstanceAs (IsProper (pullback.snd i₀ π ≫ X'.hom))
  have : IsProper (toPoint Z').left := by rw [toPoint_left]; infer_instance
  let i : Z ⟶ X := Over.homMk i₀ rfl
  let i' : Z' ⟶ X' := Over.homMk (pullback.snd i₀ π) rfl
  have : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion i₀)
  have : IsClosedImmersion i'.left := inferInstanceAs (IsClosedImmersion (pullback.snd i₀ π))
  have sqi : IsPullback (pullback.fst i₀ π) i'.left i.left π := IsPullback.of_hasPullback i₀ π
  have sqZ : IsPullback (pullback.fst i₀ π) (toPoint Z').left (toPoint Z).left πs := by
    simpa [Z, Z'] using sqi.paste_vert hX
  have hφZ := ih Z i₀ (by
    obtain ⟨x, hx⟩ := hUd.nonempty
    intro h
    have : x ∈ Set.range i₀ := h ▸ Set.mem_univ x
    rw [hri₀] at this
    exact this hx) Z' (pullback.fst i₀ π) sqZ
  have hi := (isIso_dualizingComplexBaseChange_iff_of_isClosedImmersion ℓ e sqX sqZ sqi).1 hφZ
  /- The open and closed parts are complementary. -/
  have hij : IsCompl (Set.range i'.left.base) (Set.range (j' ≫ h').left.base) := by
    have h₁ : Set.range i'.left.base = π.base ⁻¹' (U : Set X.left)ᶜ := by
      change Set.range (pullback.snd i₀ π) = _
      rw [Scheme.Pullback.range_snd, hri₀]
    have h₂ : Set.range (j' ≫ h').left.base = π.base ⁻¹' (U : Set X.left) := by
      rw [Over.comp_left, hj'₂, ← hro₀]
      exact Scheme.Pullback.range_snd o₀ π
    rw [h₁, h₂, Set.preimage_compl]
    exact isCompl_compl.symm
  have : QuasiCompact (j' ≫ h').left := by
    rw [Over.comp_left, hj'₂]
    infer_instance
  exact isIso_of_isIso_upperStar_map_of_isIso_upperShriek_map ℓ i' (j' ≫ h') hij _ hU hi

/-- **Base change of dualizing complexes of proper schemes along field extensions** (SGA 4½,
[Th. finitude]): for a proper `F`-scheme `X`, its base change `X'` along a field extension `L/F`
and an isomorphism `e : πₛ^* ℚ̄_ℓ ⟶ ℚ̄_ℓ`, the comparison `φ : π^* ω_X ⟶ ω_{X'}` of the dualizing
complexes (`ProEtale.CondensedRing.dualizingComplexBaseChange`) is an isomorphism.

The proof is by noetherian induction on the closed subschemes of `X`
(`ProEtale.CondensedRing.isIso_dualizingComplexBaseChange_of_forall_isClosedImmersion`). -/
theorem isIso_dualizingComplexBaseChange_of_fieldExtension
    {X : Over (Spec (.of F))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [IsProper (toPoint X).left]
    {X' : Over (Spec (.of L))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated X'.hom] [IsProper (toPoint X').left] {π : X'.left ⟶ X.left}
    (sqX : IsPullback π (toPoint X').left (toPoint X).left
      (Spec.map (CommRingCat.ofHom (algebraMap F L)))) :
    IsIso (dualizingComplexBaseChange ℓ e sqX) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  suffices H : ∀ S : TopologicalSpace.Closeds X.left, ∀ (Y : Over (Spec (.of F)))
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
      [IsProper (toPoint Y).left] (c : Y.left ⟶ X.left) [IsClosedImmersion c],
      Set.range c.base ⊆ S → ∀ (Y' : Over (Spec (.of L))) [LocallyOfFiniteType Y'.hom]
        [QuasiCompact Y'.hom] [IsSeparated Y'.hom] [IsProper (toPoint Y').left]
        (πY : Y'.left ⟶ Y.left) (sqY : IsPullback πY (toPoint Y').left (toPoint Y).left
          (Spec.map (CommRingCat.ofHom (algebraMap F L)))),
        IsIso (dualizingComplexBaseChange ℓ e sqY) from
    H ⊤ X (𝟙 _) (fun _ _ ↦ trivial) X' π sqX
  intro S
  induction S using WellFoundedLT.induction with
  | _ S ihS =>
  intro Y _ _ _ _ c _ hc Y' _ _ _ _ πY sqY
  refine isIso_dualizingComplexBaseChange_of_forall_isClosedImmersion ℓ e Y ?_ sqY
  intro Z _ _ _ _ i _ hi
  let S' : TopologicalSpace.Closeds X.left :=
    ⟨Set.range (i ≫ c).base, (i ≫ c).isClosedEmbedding.isClosed_range⟩
  have hS' : S' < S := by
    obtain ⟨y, hy⟩ := (Set.ne_univ_iff_exists_notMem _).1 hi
    refine lt_of_le_of_ne (fun x ⟨z, hz⟩ ↦ hc ⟨i z, by simpa using hz⟩) fun h ↦ ?_
    have hy' : c y ∈ (S : Set X.left) := hc ⟨y, rfl⟩
    rw [← h] at hy'
    obtain ⟨z, hz⟩ := hy'
    exact hy ⟨z, c.isClosedEmbedding.injective (by simpa using hz)⟩
  exact ihS S' hS' Z (i ≫ c) (fun _ h ↦ h)

end ProperScheme

end AlgebraicGeometry.ProEtale.CondensedRing
