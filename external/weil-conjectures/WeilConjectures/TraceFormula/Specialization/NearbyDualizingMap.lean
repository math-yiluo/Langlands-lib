/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.Verdier
public import WeilConjectures.TraceFormula.Specialization.PointModel

/-!

# The dualizing maps of nearby cycles over the trait

Let `S = Spec k'⟦t⟧` be the strictly henselian trait, `k'` separably closed. A model `M` of a
separated `k`-scheme `X` of finite type is a *trait model of `X` over the base*
(`NearbyCyclesModel.IsTraitModelOfBase`) if it is of finite type over `S` along `q : 𝒳 ⟶ S`,
its identification `ε : 𝒳_Ω ⟶ X` factors through a `k`-morphism `𝒳 ⟶ X` (`𝒳` being a `k`-scheme
through `q` and `S ⟶ Spec k`), and its geometric generic fibre
is the base change `X ×_k Spec Ω`. Such a model maps to the trait model of the point
(`ProEtale.CondensedRing.traitModel`) over the structure morphisms
(`NearbyCyclesModel.IsTraitModelOfBase.toTrait`), with proper exchange
`χ_a : Ψ_S Ra_* ⟶ Ra'_* Ψ_X` (`NearbyCyclesModel.IsTraitModelOfBase.pushforwardExchange`).

The *dualizing map* `θ_X : Ψ_X ω_X ⟶ ω_{X'}` (blueprint `prose-E-15` (5),
`θ_X = β_{a_X}(A)`) is the exceptional adjoint of the compact-support exchange `ν_{a_X}`, read
through the specialization unit of the trait and the base change `Lε^* ω_{X/k} ≅ ω_{𝒳_Ω/Ω}`.
The compact-support exchange is built from a relative compactification of `𝒳` over `S`, and is
independent of the choice (`NearbyCyclesModel.IsTraitModelOfBase.dualizingMap`, downstream).
A family of maps `θ` with the two properties
that characterize the dualizing maps is a `NearbyCyclesModel.NearbyDualizingData`, and its
existence is the node lemma `NearbyCyclesModel.nonempty_nearbyDualizingData` (blueprint
`prose-E-15` and the composition law `sec-Base-change-for-nearby-cycles` (4)):

* **proper models**: for `q` proper and geometric generic fibre all of `X ×_k Spec Ω`,
  `ν_{a} = χ_a⁻¹` under `Ra_! ≅ Ra_*`, so `θ_X` is the unique
  map with `tr_{X'} ∘ Ra'_*(θ_X) ∘ χ_a(ω_X) = σ⁻¹ ∘ Ψ_S(tr_X)`, `tr` the traces
  `Ra_* ω_X ≅ Ra_! Ra^! ℚ̄_ℓ ⟶ ℚ̄_ℓ` (`NearbyCyclesModel.trace`) and `σ` the specialization unit
  of the trait;
* **open restriction**: for an open sub-model `N ⊆ M` over open immersions `j`, `j'`,
  `θ_N = j'^* θ_M ∘ β_j(ω_X)` with `β_j = α_j⁻¹` and `j^! = j^*`, that is
  `ρ' ∘ j'^*(θ_M) = θ_N ∘ Ψ_N(ρ) ∘ α_j(ω_X)` for the identifications `ρ : j^* ω_X ≅ ω_Y`.

These two properties determine the family `θ`: every trait model is an open sub-model of a proper
one whose geometric generic fibre is all of `X̄ ×_k Spec Ω`
(`NearbyCyclesModel.IsTraitModelOfBase.exists_isProper_openSubmodel`), the proper exchange `χ_a`
is then invertible, and maps
`A ⟶ ω_{X'}` are determined by their traces.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable (k : Type u) [Field k] {k' : Type u} [Field k'] [Algebra k k']

/-- A nearby-cycles model `M` of a `k`-scheme `X` with special fibre `X'` is a *trait model of `X`
over the base* along `q : 𝒳 ⟶ S` and `g : 𝒳_Ω ⟶ Spec Ω` if it is of finite type over the trait
`S = Spec k'⟦t⟧` along `q` and `g`, its identification `ε` factors through a morphism `e : 𝒳 ⟶ X`
of `k`-schemes (`e ≫ (X ⟶ Spec k) = q ≫ (S ⟶ Spec k)`), and
`(ε, g) : 𝒳_Ω ⟶ X ×_k Spec Ω` is an open immersion into the base change of `X` along
`Spec Ω ⟶ S ⟶ Spec k`, so that the geometric generic fibre is an open of `X_Ω` (it is all of `X_Ω`
for the deformation to the normal cone, and an open of it for restrictions of models to opens of
the total space). -/
structure IsTraitModelOfBase {X : Over (Spec (.of k))} {X' : Over (Spec (.of k'))}
    (M : NearbyCyclesModel X.left X'.left) (q : M.total ⟶ trait k')
    (g : M.generic ⟶ Spec (.of (traitGenericField k'))) : Prop where
  isTraitModelOver : M.IsTraitModelOver q g
  exists_comp_ε : ∃ e : M.total ⟶ X.left, M.j ≫ e = M.ε ∧ e ≫ X.hom = q ≫ traitToBase k k'
  exists_openImmersion : ∃ u : M.generic ⟶ pullback X.hom (traitGenericPoint k' ≫ traitToBase k k'),
    IsOpenImmersion u ∧ u ≫ pullback.fst _ _ = M.ε ∧ u ≫ pullback.snd _ _ = g

variable {k} {X : Over (Spec (.of k))} {X' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

namespace IsTraitModelOfBase

/-- The nearby cycles of a trait model of `X` over the base preserve bounded constructible
complexes (Deligne's finiteness theorem). -/
lemma preservesBoundedConstructible (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k').Prime]
    [Fact (ringChar k' ≠ ℓ)]
    [IsSepClosed k'] (h : M.IsTraitModelOfBase k q g) :
    M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ) :=
  M.preservesBoundedConstructible_of_isTraitModel h.isTraitModelOver.isTraitModel
    (h.exists_comp_ε.imp fun _ he ↦ he.1)

/-- The morphism of models `a : M ⟶ S` from a trait model of `X` over the base to the trait
model of the point, over the structure morphisms `X ⟶ Spec k` and `X' ⟶ Spec k'`. -/
noncomputable def toTrait (h : M.IsTraitModelOfBase k q g) :
    M.Hom (traitModel k k') (toPoint X).left (toPoint X').left where
  total := q
  generic := g
  comm_j := h.isTraitModelOver.isPullback_j.w.symm
  comm_i := by rw [toPoint_left]; exact h.isTraitModelOver.isPullback_i.w.symm
  comm_ε := by
    rw [toPoint_left]
    obtain ⟨u, -, hu₁, hu₂⟩ := h.exists_openImmersion
    rw [← traitModel_j_traitToBase]
    change g ≫ traitGenericPoint k' ≫ traitToBase k k' = M.ε ≫ X.hom
    rw [← hu₁, ← hu₂, Category.assoc, Category.assoc, ← pullback.condition]

/-- A model whose geometric generic fibre is the base change of `X` (a pullback square) is a trait
model of `X` over the base. -/
lemma of_isPullback (hM : M.IsTraitModelOver q g)
    (hε : ∃ e : M.total ⟶ X.left, M.j ≫ e = M.ε ∧ e ≫ X.hom = q ≫ traitToBase k k')
    (hgen : IsPullback M.ε g X.hom (traitGenericPoint k' ≫ traitToBase k k')) :
    M.IsTraitModelOfBase k q g :=
  ⟨hM, hε, hgen.isoPullback.hom, inferInstance, hgen.isoPullback_hom_fst,
    hgen.isoPullback_hom_snd⟩

end IsTraitModelOfBase

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- The trait model of the point preserves bounded constructible complexes. -/
lemma preservesBoundedConstructible_traitModel :
    (traitModel k k').PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ) :=
  (traitModel k k').preservesBoundedConstructible_of_isTraitModel (isTraitModel_traitModel k k')
    ⟨traitToBase k k', traitModel_j_traitToBase k k'⟩

variable [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]

/-- The proper exchange `χ_a : Ψ_S Ra_* ⟶ Ra'_* Ψ_X` of the structure morphism of a trait model
of `X` over the base. -/
noncomputable def IsTraitModelOfBase.pushforwardExchange (h : M.IsTraitModelOfBase k q g) :
    boundedConstructibleLowerStar ℓ (toPoint X) ⋙
        traitSpecialization k k' (ℓ := ℓ) ⟶
      boundedConstructibleNearbyCycles (h.preservesBoundedConstructible ℓ) ⋙
        boundedConstructibleLowerStar ℓ (toPoint X') :=
  h.toTrait.boundedConstructiblePushforwardExchange ℓ (h.preservesBoundedConstructible ℓ)
    (preservesBoundedConstructible_traitModel ℓ)

/-- The trace `tr_X : Ra_* ω_X ≅ Ra_! Ra^! ℚ̄_ℓ ⟶ ℚ̄_ℓ` of a proper `k`-scheme: the counit of
`Ra_! ⊣ Ra^!` read through `Ra_! ≅ Ra_*`. -/
noncomputable def trace (Z : Over (Spec (.of k))) [LocallyOfFiniteType Z.hom]
    [QuasiCompact Z.hom] [IsSeparated Z.hom] [IsProper (toPoint Z).left] :
    (boundedConstructibleLowerStar ℓ (toPoint Z)).obj
        (dualizingComplex ℓ Z) ⟶ 𝟙_ _ :=
  (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Z)).inv.app _ ≫
    (boundedConstructibleUpperShriekAdjunction ℓ (toPoint Z)).counit.app (𝟙_ _)

instance : IsIso (traitSpecializationUnit k k' (ℓ := ℓ)) :=
  isIso_traitSpecializationUnit k k'

/-- The identification `ρ : Lj^* ω_X ≅ ω_Y` of the dualizing complexes along an open immersion
`j : Y ⟶ X` (`ProEtale.CondensedRing.dualizingComplexIsoUpperStar`), for the dualizing complexes
relative to the structure morphisms. -/
noncomputable def dualizingComplexUpperStarIso {Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] (j : Y ⟶ X)
    [IsOpenImmersion j.left] :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
        (dualizingComplex ℓ X) ≅ dualizingComplex ℓ Y :=
  (dualizingComplexIsoUpperStar ℓ j).symm

variable (k k')

/-- A *family of dualizing maps* of nearby cycles over the trait `S = Spec k'⟦t⟧`: a map
`θ_M : Ψ_M ω_X ⟶ ω_{X'}` for every trait model `M` of a `k`-scheme `X` over the base, with the
two characteristic properties of the dualizing maps `θ_M = β_a(ℚ̄_ℓ)` of blueprint
`prose-E-15` (see `NearbyCyclesModel.nonempty_nearbyDualizingData`). -/
structure NearbyDualizingData where
  /-- the dualizing map `θ_M : Ψ_M ω_X ⟶ ω_{X'}`. -/
  θ {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom]
    [QuasiCompact X'.hom] [IsSeparated X'.hom] {M : NearbyCyclesModel X.left X'.left}
    {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
    (h : M.IsTraitModelOfBase k q g) :
    (boundedConstructibleNearbyCycles (h.preservesBoundedConstructible ℓ)).obj
      (dualizingComplex ℓ X) ⟶ dualizingComplex ℓ X'
  /-- proper models whose geometric generic fibre is all of `X ×_k Spec Ω`:
  `tr_{X'} ∘ Ra'_*(θ_M) ∘ χ_a(ω_X) = σ⁻¹ ∘ Ψ_S(tr_X)`. -/
  pushforwardExchange_comp_map_θ_comp_trace {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated X'.hom] [IsProper (toPoint X).left] [IsProper (toPoint X').left]
    {M : NearbyCyclesModel X.left X'.left} {q : M.total ⟶ trait k'}
    {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (h : M.IsTraitModelOfBase k q g)
    [IsProper q] (hgen : IsPullback M.ε g X.hom (traitGenericPoint k' ≫ traitToBase k k')) :
    (h.pushforwardExchange ℓ).app (dualizingComplex ℓ X) ≫
        (boundedConstructibleLowerStar ℓ (toPoint X')).map
          (θ h) ≫ trace ℓ X' =
      (traitSpecialization k k' (ℓ := ℓ)).map (trace ℓ X) ≫
        inv (traitSpecializationUnit k k' (ℓ := ℓ))
  /-- open restriction: `ρ' ∘ j'^*(θ_M) = θ_N ∘ Ψ_N(ρ) ∘ α_j(ω_X)`. -/
  map_θ_comp_dualizingComplexUpperStarIso {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated X'.hom] {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom] {Y' : Over (Spec (.of k'))}
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    {M : NearbyCyclesModel X.left X'.left} {q : M.total ⟶ trait k'}
    {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
    {N : NearbyCyclesModel Y.left Y'.left} {qN : N.total ⟶ trait k'}
    {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}
    (hM : M.IsTraitModelOfBase k q g) (hN : N.IsTraitModelOfBase k qN gN)
    (j : Y ⟶ X) [IsOpenImmersion j.left] (j' : Y' ⟶ X') [IsOpenImmersion j'.left]
    (φ : N.Hom M j.left j'.left) [IsOpenImmersion φ.total]
    (hφ : IsPullback φ.generic N.j M.j φ.total) (hq : qN = φ.total ≫ q)
    (hg : gN = φ.generic ≫ g) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j').map (θ hM) ≫
        (dualizingComplexUpperStarIso ℓ j').hom =
      (φ.boundedConstructiblePullbackExchange ℓ (hN.preservesBoundedConstructible ℓ)
          (hM.preservesBoundedConstructible ℓ)).app (dualizingComplex ℓ X) ≫
        (boundedConstructibleNearbyCycles (hN.preservesBoundedConstructible ℓ)).map
          (dualizingComplexUpperStarIso ℓ j).hom ≫ θ hN

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
