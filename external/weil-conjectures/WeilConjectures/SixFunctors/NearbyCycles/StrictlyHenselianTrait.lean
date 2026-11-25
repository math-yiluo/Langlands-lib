/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.OpenExchange
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethGeneric
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.StrictlyHenselianBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOriginUpperStar
import WeilConjectures.Tactic.ExactModProofs

/-!

# Nearby cycles of a strictly henselian trait

Let `R` be a ring with a map `a : R ⟶ Ω` (a geometric generic point when `R` is a strictly
henselian trait and `Ω` an algebraically closed extension of its fraction field) and a map
`b : R ⟶ κ` (a special point). The spectrum `S = Spec R` is a model of `Spec Ω` with special
fibre `Spec κ` and identification `ε = 𝟙` (`NearbyCyclesModel.ofTrait`), whose nearby cycles are
`Li^* Ra_*`. A model `N` lying over `S` maps to it (`NearbyCyclesModel.Hom.toOfTrait`), and a
morphism of traits `S₂ ⟶ S₁` compatible with the points is a morphism of models
(`NearbyCyclesModel.ofTraitHom`).

**Invariance of the nearby cycles of the trait itself under change of trait.** If `ι : R₁ ⟶ R₂`
is a local homomorphism of strictly henselian local rings, `Ωᵢ` are separably closed and `b₂` has
kernel the maximal ideal, the pullback exchange `Ld^* Ψ_{S₁} ⟶ Ψ_{S₂} Lc^*` of the morphism of
traits is invertible at every complex bounded below of étale origin, with coefficients in a finite
ring `T` (`NearbyCyclesModel.isIso_pullbackExchange_ofTraitHom_app`). This is the trait case of
SGA 4½, [Th. finitude], Prop. 3.7, and the input to its step (B): both sides compute the
cohomology of the geometric generic point. It follows from
`ProEtale.CondensedRing.isIso_map_baseChangeMap_app_of_isStrictlyHenselianLocalRing`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

section Defs

variable {R Ω κ : Type u} [CommRing R] [CommRing Ω] [CommRing κ]

/-- The spectrum `S = Spec R` of a ring with a map `a : R ⟶ Ω` (the geometric generic point) and
a map `b : R ⟶ κ` (the special point), as the model of `Spec Ω` with special fibre `Spec κ`,
inclusions `Spec a` and `Spec b` and identification `ε = 𝟙`. Its nearby cycles are
`L(Spec b)^* R(Spec a)_*`. -/
noncomputable abbrev ofTrait (a : R →+* Ω) (b : R →+* κ) :
    NearbyCyclesModel (Spec (.of Ω)) (Spec (.of κ)) where
  total := Spec (.of R)
  generic := Spec (.of Ω)
  j := Spec.map (CommRingCat.ofHom a)
  i := Spec.map (CommRingCat.ofHom b)
  ε := 𝟙 _

/-- A model `N` lying over the trait `Spec R` along `q`, with geometric generic fibre over
`Spec Ω` along `g` and special fibre over `Spec κ` along `p`, maps to the trait: the model of its
geometric generic fibre (`NearbyCyclesModel.toGeneric`) maps to `NearbyCyclesModel.ofTrait a b`
over `g` and `p`. -/
abbrev Hom.toOfTrait {Y Y' : Scheme.{u}} (N : NearbyCyclesModel Y Y') (a : R →+* Ω) (b : R →+* κ)
    (q : N.total ⟶ Spec (.of R)) (g : N.generic ⟶ Spec (.of Ω)) (p : Y' ⟶ Spec (.of κ))
    (hj : N.j ≫ q = g ≫ Spec.map (CommRingCat.ofHom a))
    (hi : N.i ≫ q = p ≫ Spec.map (CommRingCat.ofHom b)) :
    N.toGeneric.Hom (ofTrait a b) g p where
  total := q
  generic := g
  comm_j := hj.symm
  comm_i := hi.symm
  comm_ε := (Category.comp_id _).trans (Category.id_comp _).symm

variable {R₁ R₂ Ω₁ Ω₂ κ₁ κ₂ : Type u} [CommRing R₁] [CommRing R₂] [CommRing Ω₁] [CommRing Ω₂]
  [CommRing κ₁] [CommRing κ₂]

/-- A morphism of traits `Spec R₂ ⟶ Spec R₁` along `ι : R₁ ⟶ R₂`, compatible with maps
`c : Ω₁ ⟶ Ω₂` of the geometric generic points and `d : κ₁ ⟶ κ₂` of the special points, as a
morphism of models `NearbyCyclesModel.ofTrait a₂ b₂ ⟶ NearbyCyclesModel.ofTrait a₁ b₁`. -/
noncomputable abbrev ofTraitHom (a₁ : R₁ →+* Ω₁) (b₁ : R₁ →+* κ₁) (a₂ : R₂ →+* Ω₂)
    (b₂ : R₂ →+* κ₂) (ι : R₁ →+* R₂) (c : Ω₁ →+* Ω₂) (d : κ₁ →+* κ₂)
    (hc : c.comp a₁ = a₂.comp ι) (hd : d.comp b₁ = b₂.comp ι) :
    (ofTrait a₂ b₂).Hom (ofTrait a₁ b₁) (Spec.map (CommRingCat.ofHom c))
      (Spec.map (CommRingCat.ofHom d)) where
  total := Spec.map (CommRingCat.ofHom ι)
  generic := Spec.map (CommRingCat.ofHom c)
  comm_j := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hc]
  comm_i := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hd]
  comm_ε := (Category.comp_id _).trans (Category.id_comp _).symm

end Defs

section Exchange

/-- A transformation `α = θi ≫ I_M(E_N^*β ≫ J_{M*}θε)` of the shape of the pullback exchange, with
`θi` and `θε` invertible, is invertible at `o` if `I_M` of `β` is invertible at `E_N o`; `β` is
given together with `β'` and a proof of `β' = β`. -/
private lemma isIso_pullbackExchange_app_aux
    {DY' DX' DTN DTM DGN DGM DY DX : Type*} [Category DY'] [Category DX'] [Category DTN]
    [Category DTM] [Category DGN] [Category DGM] [Category DY] [Category DX]
    {Fp' : DY' ⥤ DX'} {IN : DTN ⥤ DY'} {IM : DTM ⥤ DX'} {T : DTN ⥤ DTM}
    {JNs : DGN ⥤ DTN} {JMs : DGM ⥤ DTM} {G : DGN ⥤ DGM} {EN : DY ⥤ DGN} {EM : DX ⥤ DGM}
    {F : DY ⥤ DX} (θi : IN ⋙ Fp' ⟶ T ⋙ IM) [IsIso θi] (β β' : JNs ⋙ T ⟶ G ⋙ JMs)
    (h : β' = β) (θε : EN ⋙ G ⟶ F ⋙ EM) [IsIso θε]
    (α : (EN ⋙ JNs ⋙ IN) ⋙ Fp' ⟶ F ⋙ EM ⋙ JMs ⋙ IM)
    (hα : α = Functor.whiskerLeft (EN ⋙ JNs) θi ≫
      Functor.whiskerRight (Functor.whiskerLeft EN β ≫ Functor.whiskerRight θε JMs) IM)
    (o : DY) (hβ : IsIso (IM.map (β'.app (EN.obj o)))) : IsIso (α.app o) := by
  subst h hα
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp]
  infer_instance

/-- The pullback exchange of a morphism of models is invertible at `K` as soon as `Li_M^*` of the
base change morphism `Lt^* Rj_{N*} ⟶ Rj_{M*} Lg^*` of the square of geometric generic fibres is
invertible at `Lε_N^* K`. -/
private lemma Hom.isIso_pullbackExchange_app_of_isIso_map_baseChangeMap_app
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f')
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (h : IsIso (L((M.i)^*⟦Λ⟧).map
      ((baseChangeMap Λ φ.commSq_j).app (L((N.ε)^*⟦Λ⟧).obj K)))) :
    IsIso ((φ.pullbackExchange Λ).app K) :=
  isIso_pullbackExchange_app_aux (pullbackSquareComparison Λ φ.commSq_i).hom
    (mateEquiv (derivedUpperStarLowerStarAdjunction Λ N.j)
      (derivedUpperStarLowerStarAdjunction Λ M.j)
      (pullbackSquareComparison Λ φ.commSq_j).hom)
    _ (φ.baseChangeMap_commSq_j_eq_mateEquiv Λ)
    (pullbackSquareComparison Λ φ.commSq_ε).hom (φ.pullbackExchange Λ) rfl K h

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]
  {R₁ R₂ : Type u} [CommRing R₁] [IsStrictlyHenselianLocalRing R₁] [CommRing R₂]
  [IsStrictlyHenselianLocalRing R₂] {Ω₁ Ω₂ : Type u} [Field Ω₁] [IsSepClosed Ω₁] [Field Ω₂]
  [IsSepClosed Ω₂] {κ₁ κ₂ : Type u} [Field κ₁] [Field κ₂]

/-- **Invariance of the nearby cycles of a strictly henselian trait under change of trait** (the
trait case of SGA 4½, [Th. finitude], Prop. 3.7; finite coefficients). Let `ι : R₁ ⟶ R₂` be a
local homomorphism of strictly henselian local rings, `aᵢ : Rᵢ ⟶ Ωᵢ` maps to separably closed
fields and `bᵢ : Rᵢ ⟶ κᵢ` maps to fields, `b₂` with kernel the maximal ideal, compatible with
`c : Ω₁ ⟶ Ω₂` and `d : κ₁ ⟶ κ₂`. Then the pullback exchange `Ld^* Ψ_{S₁} ⟶ Ψ_{S₂} Lc^*` of the
morphism of traits `NearbyCyclesModel.ofTraitHom` is invertible at every complex `L` on
`Spec Ω₁` bounded below of étale origin, with coefficients in a finite ring `T`: after pullback to
the special point of `S₂`, the base change morphism of the square of geometric generic points is
invertible (`ProEtale.CondensedRing.isIso_map_baseChangeMap_app_of_isStrictlyHenselianLocalRing`).
-/
theorem isIso_pullbackExchange_ofTraitHom_app (a₁ : R₁ →+* Ω₁) (b₁ : R₁ →+* κ₁)
    (a₂ : R₂ →+* Ω₂) (b₂ : R₂ →+* κ₂) (ι : R₁ →+* R₂) [IsLocalHom ι] (c : Ω₁ →+* Ω₂)
    (d : κ₁ →+* κ₂) (hc : c.comp a₁ = a₂.comp ι) (hd : d.comp b₁ = b₂.comp ι)
    (hb₂ : RingHom.ker b₂ = IsLocalRing.maximalIdeal R₂)
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω₁))) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) (Spec (.of Ω₁)))))
    (hL : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) _
      ((finiteCoefficientDerivedEquivalence _ T).functor.obj L)) :
    IsIso (((ofTraitHom a₁ b₁ a₂ b₂ ι c d hc hd).pullbackExchange
      (Profinite.continuousMapRingObj T)).app L) := by
  have hL' := plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T
    (ofTrait a₁ b₁).ε hL
  have h := isIso_map_baseChangeMap_app_of_isStrictlyHenselianLocalRing T ι b₂ hb₂
    (S₁ := (ofTrait a₁ b₁).total) (S₂ := (ofTrait a₂ b₂).total) (G₁ := (ofTrait a₁ b₁).generic)
    (G₂ := (ofTrait a₂ b₂).generic) (P := Spec (.of κ₂)) rfl rfl rfl rfl rfl
    (by simp) (ofTraitHom a₁ b₁ a₂ b₂ ι c d hc hd).commSq_j (s := (ofTrait a₂ b₂).i)
    (by simp) _ hL'
  have key := Hom.isIso_pullbackExchange_app_of_isIso_map_baseChangeMap_app
    (Profinite.continuousMapRingObj T) (ofTraitHom a₁ b₁ a₂ b₂ ι c d hc hd) L
    (by exact_mod_proofs h)
  exact_mod_proofs key

end Exchange

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
