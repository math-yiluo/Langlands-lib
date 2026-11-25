/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructibleUnitIdentity
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste

/-!

# Nearby cycles and weakly étale pullback

Let `φ : M ⟶ N` be a morphism of models (`NearbyCyclesModel.Hom`) whose morphism of total spaces
`t : 𝒳_M ⟶ 𝒳_N` is weakly étale (for instance an open immersion) and whose square of geometric
generic fibres
```
𝒳_{M,η̄} --g--> 𝒳_{N,η̄}
   |j_M            |j_N
   v               v
  𝒳_M  ----t---->  𝒳_N
```
is cartesian. Then the pullback exchange `α_f : Lf'^* Ψ_N ⟶ Ψ_M Lf^*`
(`NearbyCyclesModel.Hom.pullbackExchange`) is an isomorphism
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_of_weaklyEtale`; blueprint
`prose-E-03` (1), "nearby-cycle open pullback"). Indeed `α_f` is assembled
from two pullback comparisons, which are isomorphisms, and from the mate of the pullback comparison
of the square of geometric generic fibres, which is the base change morphism
`Lt^* Rj_{N*} ⟶ Rj_{M*} Lg^*` (`NearbyCyclesModel.Hom.baseChangeMap_commSq_j_eq_mateEquiv`),
invertible by weakly étale base change
(`ProEtale.CondensedRing.isIso_baseChangeMap_of_weaklyEtale`).

The pullback exchange restricts to bounded constructible complexes
(`NearbyCyclesModel.Hom.boundedConstructiblePullbackExchange`, defined in
`WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructibleUnitIdentity`), where it is again an
isomorphism in the weakly étale case
(`NearbyCyclesModel.Hom.isIso_boundedConstructiblePullbackExchange_of_weaklyEtale`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

namespace Hom

section Abstract

/-- A transformation `α = θi ≫ I_M(E_N^*β ≫ J_{M*}θε)` of the shape of the pullback exchange, with
`θi` and `θε` invertible, is invertible if `β` is; `β` is given together with an invertible `β'`
and a proof of `β' = β`. -/
private lemma isIso_pullbackExchange_aux
    {DY' DX' DTN DTM DGN DGM DY DX : Type*} [Category DY'] [Category DX'] [Category DTN]
    [Category DTM] [Category DGN] [Category DGM] [Category DY] [Category DX]
    {Fp' : DY' ⥤ DX'} {IN : DTN ⥤ DY'} {IM : DTM ⥤ DX'} {T : DTN ⥤ DTM}
    {JNs : DGN ⥤ DTN} {JMs : DGM ⥤ DTM} {G : DGN ⥤ DGM} {EN : DY ⥤ DGN} {EM : DX ⥤ DGM}
    {F : DY ⥤ DX} (θi : IN ⋙ Fp' ⟶ T ⋙ IM) [IsIso θi] (β β' : JNs ⋙ T ⟶ G ⋙ JMs) [IsIso β']
    (h : β' = β) (θε : EN ⋙ G ⟶ F ⋙ EM) [IsIso θε]
    (α : (EN ⋙ JNs ⋙ IN) ⋙ Fp' ⟶ F ⋙ EM ⋙ JMs ⋙ IM)
    (hα : α = Functor.whiskerLeft (EN ⋙ JNs) θi ≫
      Functor.whiskerRight (Functor.whiskerLeft EN β ≫ Functor.whiskerRight θε JMs) IM) :
    IsIso α := by
  subst h hα
  infer_instance

/-- The restriction `liftExchange χ` of an invertible transformation `χ` to full subcategories is
invertible. -/
private lemma isIso_liftExchange {DY DX DY' DX' : Type*} [Category DY] [Category DX]
    [Category DY'] [Category DX'] {PY : ObjectProperty DY} {PX : ObjectProperty DX}
    {PY' : ObjectProperty DY'} {PX' : ObjectProperty DX'} {Rf : DX ⥤ DY} {Rf' : DX' ⥤ DY'}
    {ΨN : DY ⥤ DY'} {ΨM : DX ⥤ DX'} (χ : Rf ⋙ ΨN ⟶ ΨM ⋙ Rf') [IsIso χ]
    (hR : ∀ Z : PX.FullSubcategory, PY ((PX.ι ⋙ Rf).obj Z))
    (hR' : ∀ Z : PX'.FullSubcategory, PY' ((PX'.ι ⋙ Rf').obj Z))
    (hN : ∀ Z : PY.FullSubcategory, PY' ((PY.ι ⋙ ΨN).obj Z))
    (hM : ∀ Z : PX.FullSubcategory, PX' ((PX.ι ⋙ ΨM).obj Z)) :
    IsIso (liftExchange χ hR hR' hN hM) := by
  have (Z : PX.FullSubcategory) : IsIso ((liftExchange χ hR hR' hN hM).app Z) := by
    rw [← ObjectProperty.isIso_hom_iff, liftExchange_app_hom]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

end Abstract

section Ambient

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f')

/-- The base change morphism `Lt^* Rj_{N*} ⟶ Rj_{M*} Lg^*` of the square of geometric generic
fibres of a morphism of models (`ProEtale.CondensedRing.baseChangeMap`) is the mate of the pullback
comparison `Lj_M^* Lt^* ≅ Lg^* Lj_N^*` used in the pullback exchange `α_f`. -/
lemma baseChangeMap_commSq_j_eq_mateEquiv :
    baseChangeMap Λ φ.commSq_j =
      (mateEquiv (derivedUpperStarLowerStarAdjunction Λ N.j)
        (derivedUpperStarLowerStarAdjunction Λ M.j)
        (pullbackSquareComparison Λ φ.commSq_j).hom) :=
  Adjunction.exchangeRight_eq_mateEquiv _ _ _

/-- If the base change morphism `Lt^* Rj_{N*} ⟶ Rj_{M*} Lg^*` of the square of geometric generic
fibres of a morphism of models is an isomorphism, then so is the pullback exchange `α_f`: the
pullback exchange is assembled from it and from two pullback comparisons. -/
theorem isIso_pullbackExchange_of_isIso_baseChangeMap
    [IsIso (baseChangeMap Λ φ.commSq_j)] : IsIso (φ.pullbackExchange Λ) :=
  isIso_pullbackExchange_aux (pullbackSquareComparison Λ φ.commSq_i).hom
    (mateEquiv (derivedUpperStarLowerStarAdjunction Λ N.j)
      (derivedUpperStarLowerStarAdjunction Λ M.j)
      (pullbackSquareComparison Λ φ.commSq_j).hom)
    (baseChangeMap Λ φ.commSq_j) (φ.baseChangeMap_commSq_j_eq_mateEquiv Λ)
    (pullbackSquareComparison Λ φ.commSq_ε).hom (φ.pullbackExchange Λ) rfl

/-- **Nearby cycles commute with weakly étale pullback** (blueprint
`prose-E-03` (1), the "nearby-cycle open pullback"): for a morphism of models
`φ : M ⟶ N` whose morphism of total spaces `t` is weakly étale (for instance an open immersion,
or étale) and whose square of geometric generic fibres `g ≫ j_N = j_M ≫ t` is cartesian, the
pullback exchange `α_f : Lf'^* Ψ_N ⟶ Ψ_M Lf^*` is an isomorphism, on all complexes. -/
theorem isIso_pullbackExchange_of_weaklyEtale [WeaklyEtale φ.total]
    (hj : IsPullback φ.generic M.j N.j φ.total) : IsIso (φ.pullbackExchange Λ) := by
  have : WeaklyEtale φ.generic :=
    MorphismProperty.of_isPullback (P := @WeaklyEtale) hj.flip ‹_›
  have : IsIso (baseChangeMap Λ φ.commSq_j) := isIso_baseChangeMap_of_weaklyEtale Λ hj
  exact φ.isIso_pullbackExchange_of_isIso_baseChangeMap Λ

/-- **Nearby cycles commute with open restriction**: the pullback exchange of a morphism of models
whose morphism of total spaces is an open immersion and whose square of geometric generic fibres is
cartesian is an isomorphism. -/
theorem isIso_pullbackExchange_of_isOpenImmersion [IsOpenImmersion φ.total]
    (hj : IsPullback φ.generic M.j N.j φ.total) : IsIso (φ.pullbackExchange Λ) :=
  φ.isIso_pullbackExchange_of_weaklyEtale Λ hj

end Ambient

section BoundedConstructible

variable (ℓ : ℕ) [Fact ℓ.Prime] {k k' : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {M : NearbyCyclesModel X.left X'.left} {N : NearbyCyclesModel Y.left Y'.left}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}
  (φ : M.Hom N f.left f'.left)
  (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
  (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))

/-- The restricted pullback exchange is an isomorphism if the pullback exchange is. -/
theorem isIso_boundedConstructiblePullbackExchange
    [IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))] :
    IsIso (φ.boundedConstructiblePullbackExchange ℓ hM hN) := by
  rw [boundedConstructiblePullbackExchange_eq_liftExchange]
  exact isIso_liftExchange _ _ _ _ _

/-- **Nearby cycles commute with weakly étale pullback**, on bounded constructible complexes: for
a morphism of models whose morphism of total spaces is weakly étale and whose square of geometric
generic fibres is cartesian, the restricted pullback exchange is an isomorphism. -/
theorem isIso_boundedConstructiblePullbackExchange_of_weaklyEtale [WeaklyEtale φ.total]
    (hj : IsPullback φ.generic M.j N.j φ.total) :
    IsIso (φ.boundedConstructiblePullbackExchange ℓ hM hN) :=
  have := φ.isIso_pullbackExchange_of_weaklyEtale (Profinite.padicAlgClRingObj ℓ) hj
  φ.isIso_boundedConstructiblePullbackExchange ℓ hM hN

end BoundedConstructible

end Hom

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
