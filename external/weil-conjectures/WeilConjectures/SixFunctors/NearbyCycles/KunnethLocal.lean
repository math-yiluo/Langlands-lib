/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.KunnethPullback
public import WeilConjectures.SixFunctors.NearbyCycles.OpenExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleOpenCover
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomologyCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing

/-!

# The Künneth map of nearby cycles is local on the special fibre

Let `Π_{A,B} : Ψ_M A ⊠ Ψ_N B ⟶ Ψ_P (A ⊠ B)` be the Künneth map of nearby cycles
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.kunnethMap`). This file shows that
its invertibility is local on the special fibre of `P`: if every point of the special fibre has an
open neighbourhood `W` over which `M`, `N`, `P` restrict to models `M'`, `N'`, `P'` along open
immersions of the total spaces with cartesian squares of geometric generic fibres
(`NearbyCyclesModel.IsKunnethRestriction`), such that the Künneth map
`Π_{Lρ_M^* A, Lρ_N^* B}` of the restrictions is invertible, then `Π_{A,B}` is invertible
(`NearbyCyclesModel.isIso_kunnethMap_of_forall_exists_restriction`).

Indeed the pullback exchanges of open immersions are invertible
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_of_isOpenImmersion`), so the compatibility of the
Künneth map with pullbacks (`NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange`) identifies
`Π_{A,B}|_W` with `Π_{Lρ_M^* A, Lρ_N^* B}` up to isomorphisms; and a morphism of the derived
category of a noetherian scheme is invertible if it is so on the members of an open cover
(`ProEtale.CondensedRing.isIso_of_forall_exists_isIso_upperStar_map`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated ZeroObject

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-! ### Invertibility is local -/

section Local

variable {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]

/-- A complex of module objects on a scheme with noetherian underlying space vanishes as soon as
every point has an open neighbourhood on which it vanishes. -/
theorem isZero_of_forall_exists_isZero_upperStar
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (h : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧ IsZero ((L((W.ι)^*⟦Λ⟧)).obj K)) : IsZero K := by
  choose W hxW hW using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (W x : Set X))
    (fun x ↦ (W x).isOpen) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxW x⟩)
  let e := t.equivFin
  let U : Fin t.card → X.Opens := fun i ↦ W (e.symm i)
  have hU : ∀ x, ∃ i, x ∈ U i := fun x ↦ by
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨e ⟨y, hy⟩, by simpa [U] using hxy⟩
  have hH : ∀ q : ℤ, IsZero ((DerivedCategory.homologyFunctor _ q).obj K) := fun q ↦
    isZero_of_openCover Λ t.card U hU _ fun i ↦
      (((DerivedCategory.homologyFunctor _ q).map_isZero (hW (e.symm i)))).of_iso
        ((leftDerivedUpperStarHomologyIso Λ (U i).ι q).app K)
  have : IsIso (0 : (0 : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) ⟶ K) := by
    rw [DerivedCategory.isIso_iff]
    intro q
    exact ⟨⟨0, ((DerivedCategory.homologyFunctor _ q).map_isZero (isZero_zero _)).eq_of_src _ _,
      (hH q).eq_of_src _ _⟩⟩
  exact (isZero_zero _).of_iso (asIso (0 : (0 : DerivedCategory _) ⟶ K)).symm

/-- A morphism of the derived category of module objects on a scheme with noetherian underlying
space is invertible as soon as every point has an open neighbourhood on which it is. -/
theorem isIso_of_forall_exists_isIso_upperStar_map
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (f : K ⟶ L)
    (h : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧ IsIso ((L((W.ι)^*⟦Λ⟧)).map f)) : IsIso f := by
  obtain ⟨C, g, δ, hT⟩ := distinguished_cocone_triangle f
  refine (Triangle.isZero₃_iff_isIso₁ _ hT).1 (isZero_of_forall_exists_isZero_upperStar Λ C
    fun x ↦ ?_)
  obtain ⟨W, hxW, hW⟩ := h x
  exact ⟨W, hxW, Triangle.isZero₃_of_isIso₁ _ ((L((W.ι)^*⟦Λ⟧)).map_distinguished _ hT) hW⟩

end Local

namespace NearbyCyclesModel

/-! ### Restrictions of products -/

/-- If `a ≫ b ≫ c = d ≫ e ≫ g` with `b`, `c`, `d`, `e` invertible, then `a` is invertible if and
only if `g` is. -/
lemma isIso_iff_of_comp_eq {C : Type*} [Category C] {W X₁ X₂ X₃ Y₁ Y₂ : C} {a : W ⟶ X₁}
    {b : X₁ ⟶ X₂} {c : X₂ ⟶ X₃} {d : W ⟶ Y₁} {e : Y₁ ⟶ Y₂} {g : Y₂ ⟶ X₃}
    (h : a ≫ b ≫ c = d ≫ e ≫ g) [IsIso b] [IsIso c] [IsIso d] [IsIso e] :
    IsIso a ↔ IsIso g := by
  constructor
  · intro _
    have : IsIso (d ≫ e ≫ g) := h ▸ inferInstance
    have : IsIso (e ≫ g) := IsIso.of_isIso_comp_left d _
    exact IsIso.of_isIso_comp_left e g
  · intro _
    have : IsIso (a ≫ b ≫ c) := h.symm ▸ inferInstance
    exact IsIso.of_isIso_comp_right a (b ≫ c)

variable {X X' Y Y' Z Z' XU XU' YU YU' ZU ZU' : Scheme.{u}} {M : NearbyCyclesModel X X'}
  {N : NearbyCyclesModel Y Y'} {P : NearbyCyclesModel Z Z'} {MU : NearbyCyclesModel XU XU'}
  {NU : NearbyCyclesModel YU YU'} {PU : NearbyCyclesModel ZU ZU'}
  {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'} {e₁ : ZU ⟶ XU}
  {e₁' : ZU' ⟶ XU'} {e₂ : ZU ⟶ YU} {e₂' : ZU' ⟶ YU'} {r₁ : XU ⟶ X} {r₁' : XU' ⟶ X'}
  {r₂ : YU ⟶ Y} {r₂' : YU' ⟶ Y'} {r : ZU ⟶ Z} {r' : ZU' ⟶ Z'}

/-- Morphisms of models `ρ_M : M' ⟶ M`, `ρ_N : N' ⟶ N`, `ρ_P : P' ⟶ P` exhibit `φ₁', φ₂'` as a
*restriction* of `φ₁ : P ⟶ M`, `φ₂ : P ⟶ N`: the squares of morphisms of models commute, the
morphisms of total spaces are open immersions, and the squares of geometric generic fibres are
cartesian. -/
structure IsKunnethRestriction (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    (φ₁U : PU.Hom MU e₁ e₁') (φ₂U : PU.Hom NU e₂ e₂') (ρM : MU.Hom M r₁ r₁')
    (ρN : NU.Hom N r₂ r₂') (ρP : PU.Hom P r r') : Prop where
  htot₁ : φ₁U.total ≫ ρM.total = ρP.total ≫ φ₁.total
  hgen₁ : φ₁U.generic ≫ ρM.generic = ρP.generic ≫ φ₁.generic
  htot₂ : φ₂U.total ≫ ρN.total = ρP.total ≫ φ₂.total
  hgen₂ : φ₂U.generic ≫ ρN.generic = ρP.generic ≫ φ₂.generic
  hb₁ : e₁ ≫ r₁ = r ≫ f₁
  hs₁ : e₁' ≫ r₁' = r' ≫ f₁'
  hb₂ : e₂ ≫ r₂ = r ≫ f₂
  hs₂ : e₂' ≫ r₂' = r' ≫ f₂'
  isOpenImmersion_M : IsOpenImmersion ρM.total
  isOpenImmersion_N : IsOpenImmersion ρN.total
  isOpenImmersion_P : IsOpenImmersion ρP.total
  isPullback_M : IsPullback ρM.generic MU.j M.j ρM.total
  isPullback_N : IsPullback ρN.generic NU.j N.j ρN.total
  isPullback_P : IsPullback ρP.generic PU.j P.j ρP.total

-- the Künneth maps of the two products are large terms
/-- **Pullback of the Künneth map along morphisms of models with invertible exchanges**: for
morphisms of models `ρ_M : M' ⟶ M`, `ρ_N : N' ⟶ N`, `ρ_P : P' ⟶ P` compatible with
`φ₁ : P ⟶ M`, `φ₂ : P ⟶ N` and `φ₁' : P' ⟶ M'`, `φ₂' : P' ⟶ N'`, whose pullback exchanges
`α_{ρ_M}`, `α_{ρ_N}`, `α_{ρ_P}` are invertible at `A`, `B` and `A ⊠ B`, the pullback
`Lρ'^* Π_{A,B}` of the Künneth map is invertible if and only if the Künneth map
`Π_{Lρ_M^* A, Lρ_N^* B}` is.

Besides restrictions to opens
(`NearbyCyclesModel.isIso_map_kunnethMap_iff_of_isKunnethRestriction`),
this is the formal part of the generic-slicing step of Gabber's Künneth formula (blueprint
`proposition-external-kunneth-formula-nearby-cycles`, "the composition compatibility in (2)"), where
`ρ` is the base change to the generic slice of a coordinate and `α_ρ` the slicing identification (2)
(SGA 4½, [Th. finitude], §3). -/
theorem isIso_map_kunnethMap_iff_of_isIso_pullbackExchange {φ₁ : P.Hom M f₁ f₁'}
    {φ₂ : P.Hom N f₂ f₂'} {φ₁U : PU.Hom MU e₁ e₁'} {φ₂U : PU.Hom NU e₂ e₂'}
    {ρM : MU.Hom M r₁ r₁'} {ρN : NU.Hom N r₂ r₂'} {ρP : PU.Hom P r r'}
    (htot₁ : φ₁U.total ≫ ρM.total = ρP.total ≫ φ₁.total)
    (hgen₁ : φ₁U.generic ≫ ρM.generic = ρP.generic ≫ φ₁.generic)
    (htot₂ : φ₂U.total ≫ ρN.total = ρP.total ≫ φ₂.total)
    (hgen₂ : φ₂U.generic ≫ ρN.generic = ρP.generic ≫ φ₂.generic)
    (hb₁ : e₁ ≫ r₁ = r ≫ f₁) (hs₁ : e₁' ≫ r₁' = r' ≫ f₁') (hb₂ : e₂ ≫ r₂ = r ≫ f₂)
    (hs₂ : e₂' ≫ r₂' = r' ≫ f₂')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    [IsIso ((ρM.pullbackExchange Λ).app A)] [IsIso ((ρN.pullbackExchange Λ).app B)]
    [IsIso ((ρP.pullbackExchange Λ).app (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B))] :
    IsIso (L((r')^*⟦Λ⟧).map (kunnethMap Λ φ₁ φ₂ A B)) ↔
      IsIso (kunnethMap Λ φ₁U φ₂U (L((r₁)^*⟦Λ⟧).obj A) (L((r₂)^*⟦Λ⟧).obj B)) :=
  isIso_iff_of_comp_eq (map_kunnethMap_comp_pullbackExchange Λ φ₁ φ₂ φ₁U φ₂U ρM ρN ρP
    htot₁ hgen₁ htot₂ hgen₂ hb₁ hs₁ hb₂ hs₂ A B)

-- the Künneth maps of the two products are large terms
/-- **Restriction of the Künneth map**: for a restriction of the product along open immersions,
the pullback `Lρ'^* Π_{A,B}` of the Künneth map to the special fibre of the restriction is
invertible if and only if the Künneth map `Π_{Lρ_M^* A, Lρ_N^* B}` of the restriction is. -/
theorem isIso_map_kunnethMap_iff_of_isKunnethRestriction {φ₁ : P.Hom M f₁ f₁'}
    {φ₂ : P.Hom N f₂ f₂'} {φ₁U : PU.Hom MU e₁ e₁'} {φ₂U : PU.Hom NU e₂ e₂'}
    {ρM : MU.Hom M r₁ r₁'} {ρN : NU.Hom N r₂ r₂'} {ρP : PU.Hom P r r'}
    (h : IsKunnethRestriction φ₁ φ₂ φ₁U φ₂U ρM ρN ρP)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    IsIso (L((r')^*⟦Λ⟧).map (kunnethMap Λ φ₁ φ₂ A B)) ↔
      IsIso (kunnethMap Λ φ₁U φ₂U (L((r₁)^*⟦Λ⟧).obj A) (L((r₂)^*⟦Λ⟧).obj B)) := by
  have := h.isOpenImmersion_M
  have := h.isOpenImmersion_N
  have := h.isOpenImmersion_P
  have := ρM.isIso_pullbackExchange_of_isOpenImmersion Λ h.isPullback_M
  have := ρN.isIso_pullbackExchange_of_isOpenImmersion Λ h.isPullback_N
  have := ρP.isIso_pullbackExchange_of_isOpenImmersion Λ h.isPullback_P
  exact isIso_map_kunnethMap_iff_of_isIso_pullbackExchange Λ h.htot₁ h.hgen₁ h.htot₂ h.hgen₂
    h.hb₁ h.hs₁ h.hb₂ h.hs₂ A B

/-- **The invertibility of the Künneth map is local on the special fibre**: if every point of the
special fibre `Z'` of `P` lies in an open `W` over which `φ₁`, `φ₂` restrict
(`NearbyCyclesModel.IsKunnethRestriction`) to a product whose Künneth map
`Π_{Lρ_M^* A, Lρ_N^* B}` is invertible, then `Π_{A,B}` is invertible. -/
theorem isIso_kunnethMap_of_forall_exists_restriction [TopologicalSpace.NoetherianSpace Z']
    (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (h : ∀ z : Z', ∃ (W : Z'.Opens) (XU XU' YU YU' ZU : Scheme.{u})
      (MU : NearbyCyclesModel XU XU') (NU : NearbyCyclesModel YU YU')
      (PU : NearbyCyclesModel ZU W) (e₁ : ZU ⟶ XU) (e₁' : (W : Scheme.{u}) ⟶ XU')
      (e₂ : ZU ⟶ YU) (e₂' : (W : Scheme.{u}) ⟶ YU') (r₁ : XU ⟶ X) (r₁' : XU' ⟶ X')
      (r₂ : YU ⟶ Y) (r₂' : YU' ⟶ Y') (r : ZU ⟶ Z) (φ₁U : PU.Hom MU e₁ e₁')
      (φ₂U : PU.Hom NU e₂ e₂') (ρM : MU.Hom M r₁ r₁') (ρN : NU.Hom N r₂ r₂')
      (ρP : PU.Hom P r W.ι), z ∈ W ∧ IsKunnethRestriction φ₁ φ₂ φ₁U φ₂U ρM ρN ρP ∧
        IsIso (kunnethMap Λ φ₁U φ₂U (L((r₁)^*⟦Λ⟧).obj A) (L((r₂)^*⟦Λ⟧).obj B))) :
    IsIso (kunnethMap Λ φ₁ φ₂ A B) := by
  refine isIso_of_forall_exists_isIso_upperStar_map Λ _ fun z ↦ ?_
  obtain ⟨W, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, φ₁U, φ₂U, ρM, ρN, ρP, hzW, hR,
    hK⟩ := h z
  exact ⟨W, hzW, (isIso_map_kunnethMap_iff_of_isKunnethRestriction Λ hR A B).2 hK⟩

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
