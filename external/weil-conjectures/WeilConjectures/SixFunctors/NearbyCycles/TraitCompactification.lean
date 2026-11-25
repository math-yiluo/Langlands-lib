/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.StrictlyHenselianTrait
public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ProperBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerStarFullyFaithful
public import WeilConjectures.Compactification.Defs
import WeilConjectures.Tactic.ExactModProofs

/-!

# Reduction of the change of trait to proper models

Let `ι : R₁ ⟶ R₂` be a ring map with compatible maps `aᵢ : Rᵢ ⟶ Ωᵢ` (`c ∘ a₁ = a₂ ∘ ι`) and
`bᵢ : Rᵢ ⟶ κᵢ` (`d ∘ b₁ = b₂ ∘ ι`), let `N` be a model over `Spec R₁` along `q₁` (with cartesian
squares of geometric generic and special fibres), `M` its base change to `Spec R₂` and
`φ : M ⟶ N` the morphism of models (the situation of SGA 4½, [Th. finitude], Prop. 3.7).

A scheme `Z` over `Spec R₁` along `q` is a model of its geometric generic fibre `Z ×_{R₁} Ω₁` with
special fibre `Z ×_{R₁} κ₁` (`NearbyCyclesModel.ofOverTrait`); a morphism over `Spec ι` induces a
morphism of such models (`NearbyCyclesModel.ofOverTraitHom`). For a compactification
`c = (N.total ⟶[c.i] c.Z ⟶[c.g] Spec R₁)` of `q₁` (Nagata), the compactified model
`N̄ = ofOverTrait a₁ b₁ c.g` is proper over `Spec R₁`, its base change
`M̄ = ofOverTrait a₂ b₂ (c.Z ×_{R₁} Spec R₂ ⟶ Spec R₂)` maps to it by
`φ̄ = NearbyCyclesModel.compactificationHom`, and `N`, `M` are open in `N̄`, `M̄`
(`NearbyCyclesModel.Hom.toOfOverTrait`).

**Reduction to proper models.** If the pullback exchange of `φ̄` is invertible at every complex
bounded below of étale origin, so is that of `φ`
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_compactification`). Indeed nearby cycles
commute with open restriction (`NearbyCyclesModel.Hom.isIso_pullbackExchange_of_isOpenImmersion`),
so by the square law of the pullback exchanges the exchange of `φ` at `Lu^* L` is invertible if
that of `φ̄` at `L` is (`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_upperStar_of_square`); and
every `K` is `Lu^* Ru_* K` for the open immersion `u` of the geometric generic fibres, `Ru_* K`
being again of étale origin. This is the reduction to (pro)jective models at the start of the
proof of loc. cit., Prop. 3.7, with Nagata's compactification instead of a projective closure and
the direct image instead of the extension by zero.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

/-! ### The pullback exchange through a square with invertible sides -/

section Square

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' X₁ X₁' Z Z' Z₁ Z₁' : Scheme.{u}} {M : NearbyCyclesModel X X'}
  {M₁ : NearbyCyclesModel X₁ X₁'} {P : NearbyCyclesModel Z Z'} {P₁ : NearbyCyclesModel Z₁ Z₁'}
  {f₀ : Z ⟶ X} {f₀' : Z' ⟶ X'} {g : X ⟶ X₁} {g' : X' ⟶ X₁'} {k : Z ⟶ Z₁} {k' : Z' ⟶ Z₁'}
  {e : Z₁ ⟶ X₁} {e' : Z₁' ⟶ X₁'}

/-- **The pullback exchange through a square with invertible sides**: for a commutative square of
morphisms of models `φ₀ : P ⟶ M`, `ψ : M ⟶ M₁`, `ψ' : P ⟶ P₁`, `φ₁ : P₁ ⟶ M₁`, if the pullback
exchanges of `ψ` at `C` and of `ψ'` at `Le^* C` are invertible (for instance if `ψ` and `ψ'` are
open immersions of models), then the pullback exchange of `φ₀` is invertible at `Lg^* C` as soon
as that of `φ₁` is invertible at `C`. This is the square law of the pullback exchanges
(`NearbyCyclesModel.Hom.pullbackExchange_square`). -/
theorem Hom.isIso_pullbackExchange_app_upperStar_of_square (φ₀ : P.Hom M f₀ f₀')
    (ψ : M.Hom M₁ g g') (ψ' : P.Hom P₁ k k') (φ₁ : P₁.Hom M₁ e e')
    (htot : φ₀.total ≫ ψ.total = ψ'.total ≫ φ₁.total)
    (hgen : φ₀.generic ≫ ψ.generic = ψ'.generic ≫ φ₁.generic) (hb : f₀ ≫ g = k ≫ e)
    (hs : f₀' ≫ g' = k' ≫ e')
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X₁) Ab.{u + 1})
      (condensedRingObj Λ X₁)))
    (hψ : IsIso ((ψ.pullbackExchange Λ).app C))
    (hψ' : IsIso ((ψ'.pullbackExchange Λ).app (L((e)^*⟦Λ⟧).obj C)))
    (hφ₁ : IsIso ((φ₁.pullbackExchange Λ).app C)) :
    IsIso ((φ₀.pullbackExchange Λ).app (L((g)^*⟦Λ⟧).obj C)) := by
  have h : IsIso ((pullbackSquareComparison Λ (⟨hs⟩ : CommSq f₀' k' g' e')).hom.app
      ((M₁.nearbyCycles Λ).obj C) ≫ L((f₀')^*⟦Λ⟧).map ((ψ.pullbackExchange Λ).app C) ≫
        (φ₀.pullbackExchange Λ).app (L((g)^*⟦Λ⟧).obj C)) := by
    rw [Hom.pullbackExchange_square Λ φ₀ ψ ψ' φ₁ htot hgen hb hs C]
    infer_instance
  have h' := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ inferInstance h
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _
    (Functor.map_isIso L((f₀')^*⟦Λ⟧) ((ψ.pullbackExchange Λ).app C)) h'

end Square

/-! ### Models given by the fibres of a scheme over a trait -/

section OverTrait

variable {R Ω κ : Type u} [CommRing R] [CommRing Ω] [CommRing κ]

/-- A scheme `Z` over `Spec R` along `q`, as the model of its geometric generic fibre
`Z ×_R Spec Ω` (along `a : R ⟶ Ω`) with special fibre `Z ×_R Spec κ` (along `b : R ⟶ κ`), the
inclusions being the first projections and the identification `ε = 𝟙`. -/
noncomputable abbrev ofOverTrait (a : R →+* Ω) (b : R →+* κ) {Z : Scheme.{u}}
    (q : Z ⟶ Spec (.of R)) :
    NearbyCyclesModel (pullback q (Spec.map (CommRingCat.ofHom a)))
      (pullback q (Spec.map (CommRingCat.ofHom b))) where
  total := Z
  generic := pullback q (Spec.map (CommRingCat.ofHom a))
  j := pullback.fst _ _
  i := pullback.fst _ _
  ε := 𝟙 _

/-- A model `N` over `Spec R` along `q` maps to the model `ofOverTrait a b q'` of a scheme
`Z` over `Spec R` along `q'`, for `u : N.total ⟶ Z` with `u ≫ q' = q`: the map of geometric generic
fibres and of special fibres are induced by `u`. -/
noncomputable abbrev Hom.toOfOverTrait {Y Y' : Scheme.{u}} (N : NearbyCyclesModel Y Y')
    (a : R →+* Ω) (b : R →+* κ) {Z : Scheme.{u}} (q' : Z ⟶ Spec (.of R))
    (q : N.total ⟶ Spec (.of R)) (g : N.generic ⟶ Spec (.of Ω)) (p : Y' ⟶ Spec (.of κ))
    (hj : N.j ≫ q = g ≫ Spec.map (CommRingCat.ofHom a))
    (hi : N.i ≫ q = p ≫ Spec.map (CommRingCat.ofHom b)) (u : N.total ⟶ Z) (hu : u ≫ q' = q) :
    N.toGeneric.Hom (ofOverTrait a b q')
      (pullback.lift (N.j ≫ u) g (by rw [Category.assoc, hu, hj]))
      (pullback.lift (N.i ≫ u) p (by rw [Category.assoc, hu, hi])) where
  total := u
  generic := pullback.lift (N.j ≫ u) g (by rw [Category.assoc, hu, hj])
  comm_j := pullback.lift_fst _ _ _
  comm_i := pullback.lift_fst _ _ _
  comm_ε := (Category.comp_id _).trans (Category.id_comp _).symm

variable {R₁ R₂ Ω₁ Ω₂ κ₁ κ₂ : Type u} [CommRing R₁] [CommRing R₂] [CommRing Ω₁] [CommRing Ω₂]
  [CommRing κ₁] [CommRing κ₂]

/-- A morphism `v : Z₂ ⟶ Z₁` of schemes over `Spec ι : Spec R₂ ⟶ Spec R₁` induces a morphism of the
models `ofOverTrait a₂ b₂ q₂ ⟶ ofOverTrait a₁ b₁ q₁`, the maps of fibres being induced by `v` and
by `c : Ω₁ ⟶ Ω₂`, `d : κ₁ ⟶ κ₂`. -/
noncomputable abbrev ofOverTraitHom (a₁ : R₁ →+* Ω₁) (b₁ : R₁ →+* κ₁) (a₂ : R₂ →+* Ω₂)
    (b₂ : R₂ →+* κ₂) (ι : R₁ →+* R₂) (c : Ω₁ →+* Ω₂) (d : κ₁ →+* κ₂)
    (hc : c.comp a₁ = a₂.comp ι) (hd : d.comp b₁ = b₂.comp ι) {Z₁ Z₂ : Scheme.{u}}
    (q₁ : Z₁ ⟶ Spec (.of R₁)) (q₂ : Z₂ ⟶ Spec (.of R₂)) (v : Z₂ ⟶ Z₁)
    (hv : v ≫ q₁ = q₂ ≫ Spec.map (CommRingCat.ofHom ι)) :
    (ofOverTrait a₂ b₂ q₂).Hom (ofOverTrait a₁ b₁ q₁)
      (pullback.lift (pullback.fst _ _ ≫ v) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom c))
        (by
          rw [Category.assoc, hv, pullback.condition_assoc, Category.assoc,
            ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            ← CommRingCat.ofHom_comp, hc]))
      (pullback.lift (pullback.fst _ _ ≫ v) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom d))
        (by
          rw [Category.assoc, hv, pullback.condition_assoc, Category.assoc,
            ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            ← CommRingCat.ofHom_comp, hd])) where
  total := v
  generic := pullback.lift (pullback.fst _ _ ≫ v)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom c))
    (by
      rw [Category.assoc, hv, pullback.condition_assoc, Category.assoc,
        ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp, hc])
  comm_j := pullback.lift_fst _ _ _
  comm_i := pullback.lift_fst _ _ _
  comm_ε := (Category.comp_id _).trans (Category.id_comp _).symm

end OverTrait

/-! ### Reduction to proper models -/

section Compactification

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T] {R₁ R₂ Ω₁ Ω₂ κ₁ κ₂ : Type u} [CommRing R₁] [CommRing R₂] [CommRing Ω₁]
  [CommRing Ω₂] [CommRing κ₁] [CommRing κ₂] {a₁ : R₁ →+* Ω₁} {b₁ : R₁ →+* κ₁} {a₂ : R₂ →+* Ω₂}
  {b₂ : R₂ →+* κ₂} {ι : R₁ →+* R₂} {c : Ω₁ →+* Ω₂} {d : κ₁ →+* κ₂}
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- For a cartesian square `j ≫ q = g₁ ≫ s` and a factorization `q = i ≫ g`, the square formed by
the induced map `A ⟶ Z ×_S S'`, `j`, the first projection and `i` is cartesian. -/
private lemma isPullback_pullbackLift_comp {𝒞 : Type*} [Category 𝒞] {A B Z S S' : 𝒞}
    {j : A ⟶ B} {g₁ : A ⟶ S'} {q : B ⟶ S} {s : S' ⟶ S} (h : IsPullback j g₁ q s) {g : Z ⟶ S}
    [HasPullback g s] (i : B ⟶ Z) (hi : i ≫ g = q) (w : (j ≫ i) ≫ g = g₁ ≫ s) :
    IsPullback (pullback.lift (j ≫ i) g₁ w) j (pullback.fst g s) i :=
  IsPullback.of_right (by rw [pullback.lift_snd, hi]; exact h.flip) (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback g s).flip

/-- A natural transformation invertible at `F (G K)` is invertible at `K`, for an adjunction
`F ⊣ G` with invertible counit. -/
private lemma isIso_app_of_isIso_app_counit {𝒞 𝒟 ℰ : Type*} [Category 𝒞] [Category 𝒟]
    [Category ℰ] {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (adj : F ⊣ G) [IsIso adj.counit] {H H' : 𝒟 ⥤ ℰ}
    (α : H ⟶ H') (K : 𝒟) (h : IsIso (α.app (F.obj (G.obj K)))) : IsIso (α.app K) :=
  (NatTrans.isIso_app_iff_of_iso α (asIso (adj.counit.app K))).mp h

/-- **Reduction of the change of trait to proper models** (the first step of the proof of
SGA 4½, [Th. finitude], Prop. 3.7). Let `N` be a model over `Spec R₁` along a quasi-compact `q₁`,
`M` a model over `Spec R₂` along `q₂` and `φ : M ⟶ N` a morphism of models whose square of total
spaces over `Spec ι` is cartesian, with the squares of geometric generic fibres and of special
fibres cartesian and the maps of fibres over `Spec c` and `Spec d`. Let `cpt` be a
compactification of `q₁` (for instance Nagata's, `AlgebraicGeometry.NagataCompactification`, for
`q₁` separated of finite type). If the pullback exchange of the morphism `φ̄` of compactified
models (`NearbyCyclesModel.ofOverTraitHom` for `cpt.g` and its base change to `Spec R₂`, a model
proper over `Spec R₁`) is invertible at every complex bounded below of étale origin, with
coefficients in a finite ring `T`, then so is the pullback exchange of `φ` (on the models of the
geometric generic fibres). -/
theorem Hom.isIso_pullbackExchange_app_of_compactification
    (hc : c.comp a₁ = a₂.comp ι) (hd : d.comp b₁ = b₂.comp ι) (φ : M.Hom N f f')
    (q₁ : N.total ⟶ Spec (.of R₁)) [QuasiCompact q₁] (g₁ : N.generic ⟶ Spec (.of Ω₁))
    (hNj : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom a₁))) (p₁ : Y' ⟶ Spec (.of κ₁))
    (hNi : IsPullback N.i p₁ q₁ (Spec.map (CommRingCat.ofHom b₁)))
    (q₂ : M.total ⟶ Spec (.of R₂)) (g₂ : M.generic ⟶ Spec (.of Ω₂))
    (hMj : IsPullback M.j g₂ q₂ (Spec.map (CommRingCat.ofHom a₂))) (p₂ : X' ⟶ Spec (.of κ₂))
    (hMi : IsPullback M.i p₂ q₂ (Spec.map (CommRingCat.ofHom b₂)))
    (hφ : IsPullback φ.total q₂ q₁ (Spec.map (CommRingCat.ofHom ι)))
    (hgen : φ.generic ≫ g₁ = g₂ ≫ Spec.map (CommRingCat.ofHom c))
    (hs : f' ≫ p₁ = p₂ ≫ Spec.map (CommRingCat.ofHom d)) (cpt : Compactification q₁)
    (H : ∀ L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
        (pullback cpt.g (Spec.map (CommRingCat.ofHom a₁)))) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj T)
          (pullback cpt.g (Spec.map (CommRingCat.ofHom a₁))))),
      DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) _
        ((finiteCoefficientDerivedEquivalence _ T).functor.obj L) →
      IsIso (((ofOverTraitHom a₁ b₁ a₂ b₂ ι c d hc hd cpt.g
        (pullback.snd cpt.g (Spec.map (CommRingCat.ofHom ι))) (pullback.fst _ _)
        pullback.condition).pullbackExchange (Profinite.continuousMapRingObj T)).app L))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) N.generic)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) _
      ((finiteCoefficientDerivedEquivalence _ T).functor.obj K)) :
    IsIso ((φ.toGeneric.pullbackExchange (Profinite.continuousMapRingObj T)).app K) := by
  -- the open immersions of `N` into `N̄` and of `M` into `M̄`, with their cartesian squares
  have hwN : (N.j ≫ cpt.i) ≫ cpt.g = g₁ ≫ Spec.map (CommRingCat.ofHom a₁) := by
    rw [Category.assoc, ← cpt.comm, hNj.w]
  have hwφ : (φ.total ≫ cpt.i) ≫ cpt.g = q₂ ≫ Spec.map (CommRingCat.ofHom ι) := by
    rw [Category.assoc, ← cpt.comm, hφ.w]
  have : QuasiCompact cpt.i := cpt.quasiCompact_openImmersion ‹_›
  have hNsq := isPullback_pullbackLift_comp hNj cpt.i cpt.comm.symm hwN
  have hφsq := isPullback_pullbackLift_comp hφ cpt.i cpt.comm.symm hwφ
  have : IsOpenImmersion (pullback.lift (φ.total ≫ cpt.i) q₂ hwφ) :=
    MorphismProperty.of_isPullback hφsq.flip inferInstance
  have hMsq := isPullback_pullbackLift_comp hMj
    (pullback.lift (φ.total ≫ cpt.i) q₂ hwφ)
    (pullback.lift_snd _ _ _) (by rw [Category.assoc, pullback.lift_snd, hMj.w])
  have : IsOpenImmersion (pullback.lift (N.j ≫ cpt.i) g₁ hwN) :=
    MorphismProperty.of_isPullback hNsq.flip inferInstance
  have : QuasiCompact (pullback.lift (N.j ≫ cpt.i) g₁ hwN) :=
    MorphismProperty.of_isPullback hNsq.flip inferInstance
  have hC := plusEtaleOrigin_finiteCoefficientDerivedEquivalence_rightDerivedLowerStar_obj T
    (pullback.lift (N.j ≫ cpt.i) g₁ hwN) hK
  have key := Hom.isIso_pullbackExchange_app_upperStar_of_square
    (Profinite.continuousMapRingObj T) φ.toGeneric
    (Hom.toOfOverTrait N a₁ b₁ cpt.g q₁ g₁ p₁ hNj.w hNi.w cpt.i cpt.comm.symm)
    (Hom.toOfOverTrait M a₂ b₂ (pullback.snd cpt.g (Spec.map (CommRingCat.ofHom ι))) q₂ g₂ p₂
      hMj.w hMi.w (pullback.lift (φ.total ≫ cpt.i) q₂ hwφ)
      (pullback.lift_snd _ _ _))
    (ofOverTraitHom a₁ b₁ a₂ b₂ ι c d hc hd cpt.g (pullback.snd _ _) (pullback.fst _ _)
      pullback.condition)
    (pullback.lift_fst _ _ _).symm
    (by
      apply pullback.hom_ext
      · simp [reassoc_of% φ.comm_j]
      · simp [hgen])
    (by
      apply pullback.hom_ext
      · simp [reassoc_of% φ.comm_j]
      · simp [hgen])
    (by
      apply pullback.hom_ext
      · simp [reassoc_of% φ.comm_i]
      · simp [hs])
    (R((pullback.lift (N.j ≫ cpt.i) g₁ hwN)_*⟦Profinite.continuousMapRingObj T⟧).obj K)
    (by
      have := (Hom.toOfOverTrait N a₁ b₁ cpt.g q₁ g₁ p₁ hNj.w hNi.w cpt.i
        cpt.comm.symm).isIso_pullbackExchange_of_isOpenImmersion
        (Profinite.continuousMapRingObj T) hNsq
      infer_instance)
    (by
      have := (Hom.toOfOverTrait M a₂ b₂ (pullback.snd cpt.g (Spec.map (CommRingCat.ofHom ι)))
        q₂ g₂ p₂ hMj.w hMi.w
        (pullback.lift (φ.total ≫ cpt.i) q₂ hwφ)
        (pullback.lift_snd _ _ _)).isIso_pullbackExchange_of_isOpenImmersion
        (Profinite.continuousMapRingObj T) hMsq
      infer_instance)
    (by exact_mod_proofs H _ hC)
  have key' : IsIso ((φ.toGeneric.pullbackExchange (Profinite.continuousMapRingObj T)).app
      (L((pullback.lift (N.j ≫ cpt.i) g₁ hwN)^*⟦Profinite.continuousMapRingObj T⟧).obj
        (R((pullback.lift (N.j ≫ cpt.i) g₁ hwN)_*⟦Profinite.continuousMapRingObj T⟧).obj K))) := by
    exact_mod_proofs key
  exact isIso_app_of_isIso_app_counit
    (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj T)
      (pullback.lift (N.j ≫ cpt.i) g₁ hwN)) _ K key'

end Compactification

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
