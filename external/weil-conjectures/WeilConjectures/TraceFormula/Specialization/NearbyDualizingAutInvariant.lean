/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.AutActionExchange
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingGenericBaseUnique

/-!

# The dualizing maps over a generic base are invariant under Galois automorphisms

Let `M` be a trait model of `X₁` over the generic base, with structure morphisms
`q : 𝒳 ⟶ S` and `g : 𝒳_Ω ⟶ Spec Ω`, and let `ψ : M ⟶ M` be a morphism of models over the
identities which is the identity on the total space and acts on the geometric generic fibre
through a Galois automorphism `σ` of `Spec Ω` over `η`: `ψ.generic ≫ g = g ≫ σ`. Then the action
`ρ(ψ)` of `ψ` on `Ψ_M ω_{X₁}` (`NearbyCyclesModel.Hom.autAction`) fixes every dualizing map:
`ρ(ψ) ≫ θ_M = θ_M` (`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.autAction_comp_θ`).

The proof follows the uniqueness of the dualizing maps:

* for a proper model with full geometric generic fibre, the proper exchange `χ_a` intertwines
  `RΓ(ρ(ψ))` with the action of `σ` on the nearby cycles `Ψ_S` of the trait
  (`NearbyCyclesModel.Hom.pushforwardExchange_app_comp_map_autAction`), which fixes
  `Ψ_S(tr) ∘ σ_s⁻¹` (`NearbyCyclesModel.Hom.unit_comp_autAction`); so `ρ(ψ) ≫ θ_M` and `θ_M` have
  the same trace
  (`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.autAction_comp_θ_of_isProper`);
* in general, `ψ` extends to a proper model containing `M` as an open sub-model, and the pullback
  exchange `α_j` intertwines the two actions
  (`NearbyCyclesModel.Hom.pullbackExchange_app_comp_autAction_of_comm`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

/-- The action `ρ(s) : Ψ ⟶ Ψ` of a morphism of models `s` over the identities on the nearby
cycles of bounded constructible complexes: the restriction of `NearbyCyclesModel.Hom.autAction`. -/
noncomputable def Hom.boundedConstructibleAutAction
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
    {X X' : Scheme.{u}} {M : NearbyCyclesModel X X'} (s : M.Hom M (𝟙 X) (𝟙 X'))
    (hM : M.PreservesBoundedConstructible Λ) :
    boundedConstructibleNearbyCycles hM ⟶ boundedConstructibleNearbyCycles hM where
  app A := ObjectProperty.homMk (s.autAction Λ A.obj)
  naturality _ _ f := ObjectProperty.hom_ext _ (s.autAction_naturality Λ f.hom).symm

/-- The action of a self-map on bounded constructible complexes is that on the ambient derived
categories. -/
lemma Hom.boundedConstructibleAutAction_app
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
    {X X' : Scheme.{u}} {M : NearbyCyclesModel X X'} (s : M.Hom M (𝟙 X) (𝟙 X'))
    (hM : M.PreservesBoundedConstructible Λ)
    (A : Dᵇc(X)⟦Λ⟧) :
    (s.boundedConstructibleAutAction hM).app A = ObjectProperty.homMk (s.autAction Λ A.obj) :=
  rfl

section BoundedConstructible

variable (ℓ : ℕ) [Fact ℓ.Prime] {k k' : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [Field k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {M : NearbyCyclesModel X.left X'.left} {N : NearbyCyclesModel Y.left Y'.left}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- The intertwining of actions by an exchange on bounded constructible complexes, for arbitrary
ambient transformations: kept abstract so that elaboration never unfolds the ambient exchanges
and actions. -/
private lemma comp_map_autAction_aux
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (χa : R((f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
        N.nearbyCycles (Profinite.padicAlgClRingObj ℓ) ⟶
      M.nearbyCycles (Profinite.padicAlgClRingObj ℓ) ⋙
        R((f'.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧))
    (βa : ∀ E, (M.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj E ⟶
      (M.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj E)
    (βa' : ∀ E, (N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj E ⟶
      (N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj E)
    (hyp : ∀ E, χa.app E ≫ R((f'.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map (βa E) =
      βa' (R((f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj E) ≫ χa.app E)
    (χb : boundedConstructibleLowerStar ℓ f ⋙ boundedConstructibleNearbyCycles hN ⟶
      boundedConstructibleNearbyCycles hM ⋙ boundedConstructibleLowerStar ℓ f')
    (hχb : ∀ K, (χb.app K).hom = χa.app K.obj)
    (βb : boundedConstructibleNearbyCycles hM ⟶ boundedConstructibleNearbyCycles hM)
    (hβb : ∀ K, (βb.app K).hom = βa K.obj)
    (βb' : boundedConstructibleNearbyCycles hN ⟶ boundedConstructibleNearbyCycles hN)
    (hβb' : ∀ K, (βb'.app K).hom = βa' K.obj) (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    χb.app K ≫ (boundedConstructibleLowerStar ℓ f').map (βb.app K) =
      βb'.app _ ≫ χb.app K := by
  apply ObjectProperty.hom_ext
  have hR : ((boundedConstructibleLowerStar ℓ f').map (βb.app K)).hom =
      R((f'.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map (βb.app K).hom := rfl
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom, hχb,
    hβb', hR, hβb]
  exact hyp K.obj

omit [Fact (ringChar k).Prime] [Fact (ringChar k').Prime] [IsSeparated X.hom]
  [IsSeparated X'.hom] in
/-- The action of a self-map on bounded constructible complexes fixes the specialization unit if
the ambient one does: kept abstract so that elaboration never unfolds the ambient action. -/
private lemma unit_comp_autAction_aux
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (βa : ∀ E, (M.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj E ⟶
      (M.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj E)
    (hyp : M.unit _ ≫ βa _ = M.unit _)
    (βb : boundedConstructibleNearbyCycles hM ⟶ boundedConstructibleNearbyCycles hM)
    (hβb : ∀ K, (βb.app K).hom = βa K.obj) :
    boundedConstructibleUnit ℓ hM ≫ βb.app _ = boundedConstructibleUnit ℓ hM := by
  apply ObjectProperty.hom_ext
  rw [ObjectProperty.FullSubcategory.comp_hom, hβb]
  exact hyp

/-- **The bounded constructible pushforward exchange intertwines the actions of self-maps**
(`NearbyCyclesModel.Hom.pushforwardExchange_app_comp_map_autAction`). -/
lemma Hom.boundedConstructiblePushforwardExchange_app_comp_map_autAction
    (φ : M.Hom N f.left f'.left)
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (s : M.Hom M (𝟙 _) (𝟙 _)) (s' : N.Hom N (𝟙 _) (𝟙 _))
    (htot : s.total ≫ φ.total = φ.total ≫ s'.total)
    (hgen : s.generic ≫ φ.generic = φ.generic ≫ s'.generic)
    (E : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (φ.boundedConstructiblePushforwardExchange ℓ hM hN).app E ≫
        (boundedConstructibleLowerStar ℓ f').map ((s.boundedConstructibleAutAction hM).app E) =
      (s'.boundedConstructibleAutAction hN).app _ ≫
        (φ.boundedConstructiblePushforwardExchange ℓ hM hN).app E :=
  comp_map_autAction_aux ℓ hM hN _ _ _
    (φ.pushforwardExchange_app_comp_map_autAction _ s s' htot hgen)
    _ (Hom.boundedConstructiblePushforwardExchange_app_hom ℓ φ hM hN)
    _ (fun K ↦ by rw [Hom.boundedConstructibleAutAction_app, ObjectProperty.homMk_hom])
    _ (fun K ↦ by rw [Hom.boundedConstructibleAutAction_app, ObjectProperty.homMk_hom]) E

omit [Fact (ringChar k).Prime] [Fact (ringChar k').Prime] [IsSeparated X.hom]
  [IsSeparated X'.hom] in
/-- **The action of a self-map fixes the bounded constructible specialization unit**
(`NearbyCyclesModel.Hom.unit_comp_autAction`). -/
lemma Hom.boundedConstructibleUnit_comp_autAction (s : M.Hom M (𝟙 _) (𝟙 _))
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ)) :
    boundedConstructibleUnit ℓ hM ≫ (s.boundedConstructibleAutAction hM).app _ =
      boundedConstructibleUnit ℓ hM :=
  unit_comp_autAction_aux ℓ hM _ (s.unit_comp_autAction _) _
    (fun K ↦ by rw [Hom.boundedConstructibleAutAction_app, ObjectProperty.homMk_hom])

/-- The intertwining of actions by the bounded constructible pullback exchange, for arbitrary
endomorphisms of the nearby cycles: kept abstract so that elaboration never unfolds the ambient
actions. -/
private lemma pullbackExchange_comp_autAction_aux (φ : M.Hom N f.left f'.left)
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (βa : ∀ E, (M.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj E ⟶
      (M.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj E)
    (βa' : ∀ E, (N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj E ⟶
      (N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj E)
    (hyp : ∀ E, (φ.pullbackExchange _).app E ≫
        βa (L((f.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj E) =
      L((f'.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map (βa' E) ≫ (φ.pullbackExchange _).app E)
    (βb : boundedConstructibleNearbyCycles hM ⟶ boundedConstructibleNearbyCycles hM)
    (hβb : ∀ K, (βb.app K).hom = βa K.obj)
    (βb' : boundedConstructibleNearbyCycles hN ⟶ boundedConstructibleNearbyCycles hN)
    (hβb' : ∀ K, (βb'.app K).hom = βa' K.obj) (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (φ.boundedConstructiblePullbackExchange ℓ hM hN).app K ≫ βb.app _ =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f').map (βb'.app K) ≫
        (φ.boundedConstructiblePullbackExchange ℓ hM hN).app K := by
  apply ObjectProperty.hom_ext
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    Hom.boundedConstructiblePullbackExchange_app_hom, hβb]
  refine (hyp K.obj).trans ?_
  rw [← hβb']
  rfl

/-- **The bounded constructible pullback exchange intertwines the actions of self-maps**
(`NearbyCyclesModel.Hom.pullbackExchange_app_comp_autAction_of_comm`). -/
lemma Hom.boundedConstructiblePullbackExchange_app_comp_autAction
    (φ : M.Hom N f.left f'.left)
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (s : M.Hom M (𝟙 _) (𝟙 _)) (s' : N.Hom N (𝟙 _) (𝟙 _))
    (htot : s.total ≫ φ.total = φ.total ≫ s'.total)
    (hgen : s.generic ≫ φ.generic = φ.generic ≫ s'.generic)
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (φ.boundedConstructiblePullbackExchange ℓ hM hN).app K ≫
        (s.boundedConstructibleAutAction hM).app _ =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f').map
          ((s'.boundedConstructibleAutAction hN).app K) ≫
        (φ.boundedConstructiblePullbackExchange ℓ hM hN).app K :=
  pullbackExchange_comp_autAction_aux ℓ φ hM hN _ _
    (φ.pullbackExchange_app_comp_autAction_of_comm (Profinite.padicAlgClRingObj ℓ) s s' htot
      hgen)
    _ (fun K ↦ by rw [Hom.boundedConstructibleAutAction_app, ObjectProperty.homMk_hom])
    _ (fun K ↦ by rw [Hom.boundedConstructibleAutAction_app, ObjectProperty.homMk_hom]) K

end BoundedConstructible

/-- The self-map of the trait as a model of a point along `ε` given by an automorphism `σ` of the
geometric generic point over the generic point `η` fixing `ε`. -/
@[simps]
noncomputable def traitModelOfPointHom {F : Type u} [Field F] {k' : Type u} [Field k']
    (ε : Spec (.of (traitGenericField k')) ⟶ Spec (.of F))
    (σ : Spec (.of (traitGenericField k')) ⟶ Spec (.of (traitGenericField k')))
    (hσ : σ ≫ traitGenericPointToSpec k' = traitGenericPointToSpec k') (hε : σ ≫ ε = ε) :
    (traitModelOfPoint ε).Hom (traitModelOfPoint ε) (𝟙 _) (𝟙 _) where
  total := 𝟙 _
  generic := σ
  comm_j := by
    dsimp only [traitModelOfPoint]
    rw [Category.comp_id, ← traitGenericPointToSpec_traitGenericSpec, reassoc_of% hσ]
  comm_i := by simp
  comm_ε := by
    dsimp only [traitModelOfPoint]
    rw [Category.comp_id, hε]

namespace NearbyDualizingDataOfGenericBase

variable {k' : Type u} [Field k'] {ℓ : ℕ} [Fact ℓ.Prime] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- **Invariance of the dualizing maps of proper models under Galois automorphisms**: for a
proper model with full geometric generic fibre and a self-map `ψ` which is the identity on the
total space and `σ` over `η` on the geometric generic point, `ρ(ψ) ≫ θ_M = θ_M`. Both sides have
the same trace: the proper exchange `χ_a` carries `RΓ(ρ(ψ))` to the action of `σ` on `Ψ_S`, which
fixes `Ψ_S(tr) ∘ σ_s⁻¹`. -/
theorem autAction_comp_θ_of_isProper (D : NearbyDualizingDataOfGenericBase k' ℓ)
    {F : Type u} [Field F] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
    {X₁ : Over (Spec (.of F))} [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom]
    [IsSeparated X₁.hom] {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
    {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated X'.hom] [IsProper (CondensedRing.toPoint X₁).left]
    [IsProper (CondensedRing.toPoint X').left] {M : NearbyCyclesModel X₁.left X'.left}
    {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
    (h : M.IsTraitModelOfGenericBase X₁ ι q g) [IsProper q]
    (hgen : IsPullback M.ε g X₁.hom (traitGenericPointToSpec k' ≫ ι))
    (ψ : M.Hom M (𝟙 _) (𝟙 _)) (hψ : ψ.total = 𝟙 _)
    (σ : Spec (.of (traitGenericField k')) ⟶ Spec (.of (traitGenericField k')))
    (hσ : σ ≫ traitGenericPointToSpec k' = traitGenericPointToSpec k')
    (hψσ : ψ.generic ≫ g = g ≫ σ) :
    (ψ.boundedConstructibleAutAction (h.preservesBoundedConstructible (ℓ := ℓ))).app
        (dualizingComplex ℓ X₁) ≫ D.θ h = D.θ h := by
  have htr := D.pushforwardExchange_comp_map_θ_comp_trace h hgen _ hgen.w.symm
  have : IsIso ((h.pushforwardExchange ℓ _ hgen.w.symm).app (dualizingComplex ℓ X₁)) :=
    h.isIso_pushforwardExchange_app ℓ _ hgen.w.symm hgen _
  let σS := traitModelOfPointHom (traitGenericPointToSpec k' ≫ ι) σ hσ (by rw [reassoc_of% hσ])
  let actS : traitPointSpecialization (traitGenericPointToSpec k' ≫ ι) ℓ ⟶
      traitPointSpecialization (traitGenericPointToSpec k' ≫ ι) ℓ :=
    σS.boundedConstructibleAutAction (preservesBoundedConstructible_traitModelOfPoint _ ℓ)
  -- the proper exchange intertwines the actions of `ψ` and `σ`
  have hχ : (h.pushforwardExchange ℓ _ hgen.w.symm).app (dualizingComplex ℓ X₁) ≫
      (boundedConstructibleLowerStar ℓ (CondensedRing.toPoint X')).map
        ((ψ.boundedConstructibleAutAction (h.preservesBoundedConstructible (ℓ := ℓ))).app
          (dualizingComplex ℓ X₁)) =
      actS.app _ ≫ (h.pushforwardExchange ℓ _ hgen.w.symm).app (dualizingComplex ℓ X₁) := by
    have htot : ψ.total ≫ (h.toPoint _ hgen.w.symm).total =
        (h.toPoint _ hgen.w.symm).total ≫ σS.total := by
      rw [hψ, Category.id_comp]
      exact (Category.comp_id _).symm
    exact (h.toPoint _ hgen.w.symm).boundedConstructiblePushforwardExchange_app_comp_map_autAction
      ℓ _ _ ψ σS htot hψσ _
  -- the action of `σ` fixes the specialization unit
  have hunit : traitPointSpecializationUnit (traitGenericPointToSpec k' ≫ ι) ℓ ≫ actS.app _ =
      traitPointSpecializationUnit (traitGenericPointToSpec k' ≫ ι) ℓ := by
    exact Hom.boundedConstructibleUnit_comp_autAction ℓ σS _
  have hunit' : actS.app _ ≫ inv (traitPointSpecializationUnit (traitGenericPointToSpec k' ≫ ι) ℓ) =
      inv (traitPointSpecializationUnit (traitGenericPointToSpec k' ≫ ι) ℓ) := by
    rw [← cancel_epi (traitPointSpecializationUnit (traitGenericPointToSpec k' ≫ ι) ℓ),
      reassoc_of% hunit]
  refine eq_of_map_comp_trace_eq ℓ X' ?_
  rw [← cancel_epi ((h.pushforwardExchange ℓ _ hgen.w.symm).app (dualizingComplex ℓ X₁)),
    Functor.map_comp, Category.assoc, reassoc_of% hχ, htr]
  rw [← actS.naturality_assoc, hunit']

/-- **Invariance of the dualizing maps under Galois automorphisms** (blueprint
`lemma-nearby-duality-slice--1`, "the map `θ`"): for a trait model `M` of `X₁` over the generic
base and a self-map `ψ` of `M` over the identities which is the identity on the total space and
acts on the geometric generic point through an automorphism `σ` of `Spec Ω` over `η`
(`ψ.generic ≫ g = g ≫ σ`), the action `ρ(ψ)` of `ψ` on `Ψ_M ω_{X₁}` fixes the dualizing map:
`ρ(ψ) ≫ θ_M = θ_M`. The model is an open sub-model of a proper model with full geometric generic
fibre, to which `ψ` extends (by `σ` on the geometric generic fibre); the dualizing map of the
proper model is invariant
(`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.autAction_comp_θ_of_isProper`),
and open restriction carries this invariance to `M`, the pullback exchange `α_j` intertwining
the two actions. -/
theorem autAction_comp_θ (D : NearbyDualizingDataOfGenericBase k' ℓ)
    {F : Type u} [Field F] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
    {X₁ : Over (Spec (.of F))} [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom]
    [IsSeparated X₁.hom] {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
    {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated X'.hom] {M : NearbyCyclesModel X₁.left X'.left}
    {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
    (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    (ψ : M.Hom M (𝟙 _) (𝟙 _)) (hψ : ψ.total = 𝟙 _)
    (σ : Spec (.of (traitGenericField k')) ⟶ Spec (.of (traitGenericField k')))
    (hσ : σ ≫ traitGenericPointToSpec k' = traitGenericPointToSpec k')
    (hψσ : ψ.generic ≫ g = g ≫ σ) :
    (ψ.boundedConstructibleAutAction (h.preservesBoundedConstructible (ℓ := ℓ))).app
        (dualizingComplex ℓ X₁) ≫ D.θ h = D.θ h := by
  obtain ⟨Xc, _, _, _, _, Xc', _, _, _, _, Mc, qc, gc, hc, hcgen, _, _, j, _, j', _, φ, _, hφ,
    hq, hg⟩ := h.exists_isProper_openSubmodel
  have hcj := hc.isTraitModelOver.isPullback_j
  -- the extension `ψc` of `ψ` to the proper model, by `σ` on the geometric generic fibre
  let ψcg : Mc.generic ⟶ Mc.generic := hcj.lift Mc.j (gc ≫ σ) (by
    rw [hcj.w, Category.assoc, ← traitGenericPointToSpec_traitGenericSpec, reassoc_of% hσ])
  have hψcj : ψcg ≫ Mc.j = Mc.j := hcj.lift_fst _ _ _
  have hψcg : ψcg ≫ gc = gc ≫ σ := hcj.lift_snd _ _ _
  have hψcε : ψcg ≫ Mc.ε = Mc.ε := by
    obtain ⟨w, -, -, hw⟩ := hc.exists_openImmersion_genericFibre
    have hfi : ψcg ≫ genericFibreInclusion Mc qc gc hcj.w = genericFibreInclusion Mc qc gc hcj.w :=
      pullback.hom_ext (by rw [Category.assoc, genericFibreInclusion_fst, hψcj])
        (by rw [Category.assoc, genericFibreInclusion_snd, reassoc_of% hψcg, hσ])
    rw [← hw, reassoc_of% hfi]
  let ψc : Mc.Hom Mc (𝟙 _) (𝟙 _) :=
    { total := 𝟙 _
      generic := ψcg
      comm_j := by rw [hψcj, Category.comp_id]
      comm_i := by simp
      comm_ε := by rw [hψcε, Category.comp_id] }
  have hprop := autAction_comp_θ_of_isProper D hc hcgen ψc rfl σ hσ hψcg
  -- `φ` intertwines `ψ` and `ψc`
  have htot : ψ.total ≫ φ.total = φ.total ≫ ψc.total := by
    rw [hψ, Category.id_comp]
    exact (Category.comp_id _).symm
  have hψcgen : ψc.generic = ψcg := rfl
  have hgen : ψ.generic ≫ φ.generic = φ.generic ≫ ψc.generic :=
    hcj.hom_ext
      (by rw [hψcgen, Category.assoc, Category.assoc, hψcj, φ.comm_j, ← Category.assoc, ψ.comm_j,
        hψ, Category.comp_id])
      (by rw [hψcgen, Category.assoc, Category.assoc, hψcg, ← hg, hψσ, hg, Category.assoc])
  have hα := φ.boundedConstructiblePullbackExchange_app_comp_autAction ℓ
    (h.preservesBoundedConstructible (ℓ := ℓ)) (hc.preservesBoundedConstructible (ℓ := ℓ)) ψ ψc
    htot hgen (dualizingComplex ℓ Xc)
  have e := D.map_θ_comp_dualizingComplexUpperStarIso hc h j j' φ hφ hq hg
  have : IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ)) :=
    φ.isIso_pullbackExchange_of_isOpenImmersion _ hφ
  have : IsIso (φ.boundedConstructiblePullbackExchange ℓ
      (h.preservesBoundedConstructible (ℓ := ℓ)) (hc.preservesBoundedConstructible (ℓ := ℓ))) :=
    φ.isIso_boundedConstructiblePullbackExchange ℓ _ _
  rw [← cancel_epi
      ((boundedConstructibleNearbyCycles (h.preservesBoundedConstructible (ℓ := ℓ))).map
        (dualizingComplexUpperStarIso ℓ j).hom),
    ← cancel_epi ((φ.boundedConstructiblePullbackExchange ℓ
      (h.preservesBoundedConstructible (ℓ := ℓ)) (hc.preservesBoundedConstructible (ℓ := ℓ))).app
        (dualizingComplex ℓ Xc)),
    (ψ.boundedConstructibleAutAction (h.preservesBoundedConstructible (ℓ := ℓ))).naturality_assoc,
    reassoc_of% hα, ← e, ← Functor.map_comp_assoc, hprop]

end NearbyDualizingDataOfGenericBase

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
