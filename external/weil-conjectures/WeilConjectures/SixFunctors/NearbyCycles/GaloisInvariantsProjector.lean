/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisContinuity

/-!

# The projector onto the Galois invariants of nearby cycles

Let `N` be a model of `X` with special fibre `X'`, `h : N.generic ⟶ Spec L`, `Ω/L` a Galois
extension whose finite Galois subextensions have degrees invertible in a finite discrete
commutative ring `T₀`, and `Λ = C(-, T₀)`. For `C` with `Lε^* C` bounded below of étale origin,
the pullback exchange `α : Ψ_N C ⟶ Ψ_{N_Ω} C` of the projection from the Galois layer has a
retraction `r` whose idempotent `e = r ≫ α` is the projector onto *all* the `Gal(Ω/L)`-invariants,
in the following cohomological form: after pullback along any `f' : Z ⟶ X'`, every map out of
`Hᵠ(Lf'^* Ψ_{N_Ω} C)` which is invariant under a family of elements of `Gal(Ω/L)` restricting
onto every finite Galois group `Gal(L'/L)` is fixed by `Hᵠ(Lf'^* e)`
(`exists_retraction_pullbackExchange_galoisLayerHom_of_plusEtaleOrigin_projector`, in the
namespace `NearbyCyclesModel`).

The retraction is induced by the derived normalized trace of the Galois tower
(`AlgebraicGeometry.ProEtale.GaloisTower.derivedTrace`). By continuity
(`NearbyCyclesModel.nonempty_isColimit_homology_nearbyCycles_galoisTower`), the cohomology sheaf is
the colimit of those of the finite layers `L'`, on which `e` acts as the average of the actions of
`Gal(L'/L)` (`AlgebraicGeometry.ProEtale.GaloisTower.map_derivedTrace_comp_unit_comp`); the
averaging argument itself is the abstract `CategoryTheory.map_comp_eq_of_isColimit_mapCocone`.
-/

@[expose] public section

-- several lemmas do not need all the instances of the section variables
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

/-- **Averaging over a colimit.** Let `D` be an additive functor such that `D` of a cocone `c` is
a colimit, `E` and `u k` endomorphisms of `c.pt`, and `t j`, `v j a` endomorphisms of the terms of
the diagram such that `c_j ≫ E = t j ≫ c_j`, `|Γ_j| • t j = ∑ a, v j a` and every `v j a ≫ c_j`
is `c_j ≫ u k` for some `k`. Then every map `φ` out of `D c.pt` which is invariant under the
`D (u k)` is fixed by `D E`, provided the `|Γ_j|` are invertible on its target. -/
lemma map_comp_eq_of_isColimit_mapCocone {J 𝒞 𝒜 : Type*} [Category J] [Category 𝒞]
    [Preadditive 𝒞] [Category 𝒜] [Preadditive 𝒜] (D : 𝒞 ⥤ 𝒜) [D.Additive] {F : J ⥤ 𝒞}
    (c : Cocone F) (hc : IsColimit (D.mapCocone c)) (E : c.pt ⟶ c.pt) {κ : Type*}
    (u : κ → (c.pt ⟶ c.pt)) {Γ : J → Type*} [∀ j, Fintype (Γ j)]
    (t : ∀ j, F.obj j ⟶ F.obj j) (v : ∀ j, Γ j → (F.obj j ⟶ F.obj j))
    (hE : ∀ j, c.ι.app j ≫ E = t j ≫ c.ι.app j)
    (ht : ∀ j, Fintype.card (Γ j) • t j = ∑ a, v j a)
    (hv : ∀ j a, ∃ k, v j a ≫ c.ι.app j = c.ι.app j ≫ u k)
    {W : 𝒜} (hW : ∀ j, IsIso (Fintype.card (Γ j) • 𝟙 W)) (φ : D.obj c.pt ⟶ W)
    (hφ : ∀ k, D.map (u k) ≫ φ = φ) : D.map E ≫ φ = φ := by
  refine hc.hom_ext fun j ↦ ?_
  have := hW j
  have h (a : Γ j) : D.map (v j a) ≫ D.map (c.ι.app j) ≫ φ = D.map (c.ι.app j) ≫ φ := by
    obtain ⟨k, hk⟩ := hv j a
    rw [← D.map_comp_assoc, hk, D.map_comp, Category.assoc, hφ]
  rw [Functor.mapCocone_ι_app, ← cancel_mono (Fintype.card (Γ j) • 𝟙 W), Preadditive.comp_nsmul,
    Preadditive.comp_nsmul, Category.comp_id, Category.comp_id, ← D.map_comp_assoc, hE,
    D.map_comp, Category.assoc, ← Preadditive.nsmul_comp, ← D.map_nsmul, ht, D.map_sum,
    Preadditive.sum_comp, Finset.sum_congr rfl fun a _ ↦ h a, Finset.sum_const,
    Finset.card_univ]

/-- Conjugation by an isomorphism `κ` and fixed maps: `φ` is fixed by `H₂ (H₁ (κ⁻¹ ≫ x ≫ κ))` iff
`H₂ (H₁ κ) ≫ φ` is fixed by `H₂ (H₁ x)`. -/
lemma map_map_conj_comp_eq_iff {C D A : Type*} [Category C] [Category D] [Category A]
    (H₁ : C ⥤ D) (H₂ : D ⥤ A) {P Q : C} (κ : P ≅ Q) (x : P ⟶ P) {W : A}
    (φ : H₂.obj (H₁.obj Q) ⟶ W) :
    H₂.map (H₁.map (κ.inv ≫ x ≫ κ.hom)) ≫ φ = φ ↔
      H₂.map (H₁.map x) ≫ H₂.map (H₁.map κ.hom) ≫ φ = H₂.map (H₁.map κ.hom) ≫ φ := by
  rw [H₁.map_comp, H₁.map_comp, H₂.map_comp, H₂.map_comp, Category.assoc, Category.assoc]
  exact Iso.inv_comp_eq ((H₁ ⋙ H₂).mapIso κ)

/-- `CategoryTheory.exists_retraction_of_eq_comp_map_comp_of_invariant`, with the idempotent of
the retraction made explicit: `r ≫ α = κ⁻¹ ≫ F₂ (F₁ (R ≫ η)) ≫ κ`. -/
lemma exists_retraction_of_eq_comp_map_comp_of_invariant_eq {C D E : Type*} [Category C]
    [Category D] [Category E] (F₁ : C ⥤ D) (F₂ : D ⥤ E) {A T : C} {W : D} {P : E}
    (α : P ⟶ F₂.obj W) (i : P ≅ F₂.obj (F₁.obj A)) (c : F₁.obj T ⟶ W)
    (κ : F₂.obj (F₁.obj T) ≅ F₂.obj W) (hκ : κ.hom = F₂.map c) (η : A ⟶ T) (R : T ⟶ A)
    (hα : α = i.hom ≫ F₂.map (F₁.map η ≫ c)) (hR : η ≫ R = 𝟙 A) {ι : Type*}
    (u : ι → (T ⟶ T)) (ρ : ι → (F₂.obj W ⟶ F₂.obj W))
    (hρ : ∀ σ, ρ σ = κ.inv ≫ F₂.map (F₁.map (u σ)) ≫ κ.hom) (hinv : ∀ σ, u σ ≫ R = R) :
    ∃ r, α ≫ r = 𝟙 P ∧ (∀ σ, ρ σ ≫ (r ≫ α) = r ≫ α) ∧
      r ≫ α = κ.inv ≫ F₂.map (F₁.map (R ≫ η)) ≫ κ.hom := by
  rw [F₂.map_comp, ← hκ] at hα
  have he : (κ.inv ≫ F₂.map (F₁.map R) ≫ i.inv) ≫ α =
      κ.inv ≫ F₂.map (F₁.map (R ≫ η)) ≫ κ.hom := by
    rw [hα]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.map_comp]
  refine ⟨κ.inv ≫ F₂.map (F₁.map R) ≫ i.inv, ?_, fun σ ↦ ?_, he⟩
  · rw [hα]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← F₂.map_comp_assoc, ← F₁.map_comp, hR, F₁.map_id, F₂.map_id, Category.id_comp,
      Iso.hom_inv_id]
  · rw [he, hρ]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← F₂.map_comp_assoc, ← F₁.map_comp, ← Category.assoc (u σ), hinv]

/-- Transport an invariant retraction along isomorphisms, retaining its projector formula. -/
private lemma exists_invariant_retraction_of_conjugate_eq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A T : C} {P Q : D} (α : P ⟶ Q) (R : T ⟶ A) (η : A ⟶ T)
    (hR : η ≫ R = 𝟙 A) (i : P ≅ F.obj A) (κ : F.obj T ≅ Q)
    (hα : α = i.hom ≫ F.map η ≫ κ.hom) {ι : Type*} (u : ι → (T ⟶ T))
    (hinv : ∀ σ, u σ ≫ R = R) (ρ : ι → (Q ⟶ Q)) (hfix : ∀ σ, α ≫ ρ σ = α)
    (hρ : ∀ σ, ρ σ = κ.inv ≫ F.map (u σ) ≫ κ.hom) :
    ∃ r, α ≫ r = 𝟙 P ∧
      (∀ σ, ρ σ ≫ (r ≫ α) = r ≫ α ∧ (r ≫ α) ≫ ρ σ = r ≫ α) ∧
      r ≫ α = κ.inv ≫ F.map (R ≫ η) ≫ κ.hom := by
  refine ⟨κ.inv ≫ F.map R ≫ i.inv, ?_, fun σ ↦ ⟨?_, ?_⟩, ?_⟩
  · rw [hα]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← F.map_comp_assoc, hR, F.map_id,
      Category.id_comp, Iso.hom_inv_id]
  · rw [hρ]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← F.map_comp_assoc, hinv]
  · rw [Category.assoc, hfix]
  · rw [hα]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, F.map_comp]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.GaloisTower

open Scheme CondensedRing

variable {X Yinf : Scheme.{u}} {ginf : Yinf ⟶ X} [WeaklyEtale ginf] (T : GaloisTower ginf)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (hd : ∀ (j : T.J)
    (N : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      IsIso (Fintype.card (T.Γ j) • 𝟙 N))

/-- The normalized trace times the order of the Galois group is the trace. -/
lemma card_smul_normTrace
    (M : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (j : T.J) : Fintype.card (T.Γ j) • T.normTrace Λ M hd j = (T.levelTrace Λ j).app M := by
  have := hd j M
  rw [normTrace, normalizedTrace, ← Preadditive.comp_nsmul, ← Category.id_comp (inv _),
    ← Preadditive.nsmul_comp, IsIso.hom_inv_id, Category.comp_id]

/-- The normalized trace followed by the unit at the level `j` is the average of the Galois
action: `|Γ_j| • (t_j ≫ u_j) = ∑ a, a`. -/
lemma card_smul_normTrace_comp_levelUnit
    (M : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (j : T.J) :
    Fintype.card (T.Γ j) • (T.normTrace Λ M hd j ≫ (T.levelUnit Λ j).app M) =
      ∑ a, (T.levelAction Λ j a).app M := by
  rw [← Preadditive.nsmul_comp, T.card_smul_normTrace Λ hd, ← NatTrans.comp_app,
    T.levelTrace_comp_levelUnit, NatTrans.app_sum]

/-- The normalized trace of the tower followed by the unit, restricted to the level `j`, is the
normalized trace of the level `j` followed by its unit. -/
lemma infTransport_comp_trace_comp_infUnit
    (M : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hc : IsColimit (T.moduleCocone Λ M)) (j : T.J) :
    T.infTransport Λ M j ≫ T.trace Λ M hd hc ≫ (infUnit Λ ginf).app M =
      (T.normTrace Λ M hd j ≫ (T.levelUnit Λ j).app M) ≫ T.infTransport Λ M j := by
  rw [Category.assoc, T.levelUnit_app_comp_infTransport, ← Category.assoc,
    T.infTransport_comp_trace]

variable (K : CochainComplex
    (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)

/-- The endomorphism `t_j ≫ u_j` of the complex `g_{j*} g_j^* K` of the level `j`, for the
normalized trace `t_j` and the unit `u_j`. -/
noncomputable def complexNormTraceUnit (j : T.J) :
    ((T.levelFunctor Λ j).mapHomologicalComplex _).obj K ⟶
      ((T.levelFunctor Λ j).mapHomologicalComplex _).obj K where
  f n := T.normTrace Λ (K.X n) hd j ≫ (T.levelUnit Λ j).app (K.X n)
  comm' i i' _ := by
    simp only [Functor.mapHomologicalComplex_obj_d, Category.assoc]
    rw [← (T.levelUnit Λ j).naturality, Functor.id_map, ← Category.assoc,
      ← T.normTrace_naturality Λ hd (K.d i i') j, Category.assoc]

variable (hc : ∀ n, IsColimit (T.moduleCocone Λ (K.X n))) (a : ℤ) [K.IsStrictlyGE a]
  (hK : ∀ n, ((ginf)_*⟦Λ⟧).rightAcyclic (((ginf)^*⟦Λ⟧).obj (K.X n)))
  (C : DerivedCategory
    (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
  (e : DerivedCategory.Q.obj K ≅ C)

/-- **The derived normalized trace** `Rg_{∞*} Lg_∞^* C ⟶ C` of a Galois tower, for `C ≅ K` with `K`
a bounded below complex such that at every term `g_{∞*} g_∞^* Kⁿ` is the colimit of the finite
levels and `g_∞^* Kⁿ` is `g_{∞*}`-acyclic: the levelwise normalized trace
`GaloisTower.complexTrace`, through `Adjunction.derivedUnitIso`. -/
noncomputable def derivedTrace :
    R((ginf)_*⟦Λ⟧).obj (L((ginf)^*⟦Λ⟧).obj C) ⟶ C :=
  R((ginf)_*⟦Λ⟧).map (L((ginf)^*⟦Λ⟧).map e.inv) ≫
    Adjunction.derivedUnitRetraction K a hK (T.complexTrace Λ hd K hc) ≫ e.hom

/-- The derived normalized trace is a retraction of the derived unit. -/
lemma unit_app_comp_derivedTrace :
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ ginf).unit.app C ≫
      T.derivedTrace Λ hd K hc a hK C e = 𝟙 C := by
  have hR₁ : (CondensedRing.derivedUpperStarLowerStarAdjunction Λ ginf).unit.app
      (DerivedCategory.Q.obj K) ≫
        Adjunction.derivedUnitRetraction K a hK (T.complexTrace Λ hd K hc) =
          𝟙 (DerivedCategory.Q.obj K) :=
    Adjunction.derivedAdjunction_unit_app_comp_derivedUnitRetraction K a hK _
      (CondensedRing.upperStarLowerStarAdjunction Λ ginf) (T.unit_comp_complexTrace Λ hd K hc)
  have hn := (CondensedRing.derivedUpperStarLowerStarAdjunction Λ ginf).unit.naturality e.inv
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at hn
  rw [derivedTrace, ← reassoc_of% hn, reassoc_of% hR₁, Iso.inv_hom_id]

/-- The derived normalized trace is invariant under the derived unit transports along the
automorphisms of `Y_∞` over `X` compatible with the Galois actions. -/
lemma derivedUnitTransport_comp_derivedTrace (σ : Yinf ⟶ Yinf) (hσ : σ ≫ ginf = ginf)
    (hσj : ∀ j, ∃ a, σ ≫ T.π j = T.π j ≫ T.ρ j a) :
    derivedUnitTransport Λ σ hσ hσ C ≫ T.derivedTrace Λ hd K hc a hK C e =
      T.derivedTrace Λ hd K hc a hK C e := by
  have hR₂ : derivedUnitTransport Λ σ hσ hσ (DerivedCategory.Q.obj K) ≫
      Adjunction.derivedUnitRetraction K a hK (T.complexTrace Λ hd K hc) =
        Adjunction.derivedUnitRetraction K a hK (T.complexTrace Λ hd K hc) := by
    have h := derivedUnitIso_hom_comp_derivedUnitTransport_self Λ ginf σ hσ K a hK
    rw [Adjunction.derivedUnitRetraction, ← cancel_epi
      (Adjunction.derivedUnitIso (f := (ginf)^*⟦Λ⟧) (g := (ginf)_*⟦Λ⟧) K a hK).hom,
      reassoc_of% h]
    simp only [Iso.hom_inv_id_assoc]
    erw [← Functor.map_comp, T.unitTransport_comp_complexTrace Λ hd K hc σ hσ hσj]
  have hn := derivedUnitTransport_naturality Λ σ hσ hσ e.inv
  rw [derivedTrace, ← reassoc_of% hn, reassoc_of% hR₂]

/-- The isomorphism `g_{∞*} g_∞^* K ≅ Rg_{∞*} Lg_∞^* C` in the derived category. -/
noncomputable def derivedTraceIso :
    DerivedCategory.Q.obj (((ginf)_*⟦Λ⟧.mapHomologicalComplex _).obj
        (((ginf)^*⟦Λ⟧.mapHomologicalComplex _).obj K)) ≅
      R((ginf)_*⟦Λ⟧).obj (L((ginf)^*⟦Λ⟧).obj C) :=
  Adjunction.derivedUnitIso (f := (ginf)^*⟦Λ⟧) (g := (ginf)_*⟦Λ⟧) K a hK ≪≫
    R((ginf)_*⟦Λ⟧).mapIso (L((ginf)^*⟦Λ⟧).mapIso e)

/-- Through `GaloisTower.derivedTraceIso`, the idempotent of the derived normalized trace is the
levelwise one. -/
lemma derivedTraceIso_hom_comp_derivedTrace_comp_unit :
    (derivedTraceIso Λ K a hK C e).hom ≫ T.derivedTrace Λ hd K hc a hK C e ≫
        (CondensedRing.derivedUpperStarLowerStarAdjunction Λ ginf).unit.app C =
      DerivedCategory.Q.map (T.complexTrace Λ hd K hc ≫
          ((CondensedRing.upperStarLowerStarAdjunction Λ ginf).mapHomologicalComplex _).unit.app
            K) ≫
        (derivedTraceIso Λ K a hK C e).hom := by
  have hn := (CondensedRing.derivedUpperStarLowerStarAdjunction Λ ginf).unit.naturality e.hom
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at hn
  have hR : Adjunction.derivedUnitRetraction K a hK (T.complexTrace Λ hd K hc) ≫
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ ginf).unit.app
        (DerivedCategory.Q.obj K) =
      (Adjunction.derivedUnitIso (f := (ginf)^*⟦Λ⟧) (g := (ginf)_*⟦Λ⟧) K a hK).inv ≫
        DerivedCategory.Q.map (T.complexTrace Λ hd K hc ≫
          ((CondensedRing.upperStarLowerStarAdjunction Λ ginf).mapHomologicalComplex _).unit.app
            K) ≫
        (Adjunction.derivedUnitIso (f := (ginf)^*⟦Λ⟧) (g := (ginf)_*⟦Λ⟧) K a hK).hom :=
    Adjunction.derivedUnitRetraction_comp_derivedAdjunction_unit_app K a hK
      (T.complexTrace Λ hd K hc) (CondensedRing.upperStarLowerStarAdjunction Λ ginf)
  simp only [derivedTraceIso, derivedTrace, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  have hcancel : R((ginf)_*⟦Λ⟧).map (L((ginf)^*⟦Λ⟧).map e.hom) ≫
      R((ginf)_*⟦Λ⟧).map (L((ginf)^*⟦Λ⟧).map e.inv) = 𝟙 _ := by
    rw [← Functor.map_comp, ← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id]
  simp only [reassoc_of% hcancel, hn, reassoc_of% hR, Iso.hom_inv_id_assoc]

/-- Through `GaloisTower.derivedTraceIso`, the derived unit transports are the levelwise ones. -/
lemma derivedTraceIso_hom_comp_derivedUnitTransport (σ : Yinf ⟶ Yinf) (hσ : σ ≫ ginf = ginf) :
    (derivedTraceIso Λ K a hK C e).hom ≫ derivedUnitTransport Λ σ hσ hσ C =
      DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (unitTransport Λ σ hσ hσ) _).app K) ≫
        (derivedTraceIso Λ K a hK C e).hom := by
  have hn := derivedUnitTransport_naturality Λ σ hσ hσ e.hom
  have h := derivedUnitIso_hom_comp_derivedUnitTransport_self Λ ginf σ hσ K a hK
  simp only [derivedTraceIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [hn, reassoc_of% h]

/-- **The derived normalized trace is the projector onto the invariants**, on any additive functor
`Φ` such that `Φ (Q (g_{∞*} g_∞^* K))` is the colimit of the finite levels: every map `φ` out of
`Φ (Rg_{∞*} Lg_∞^* C)` which is invariant under the derived unit transports along a family of
automorphisms `σ k` of `Y_∞` covering every element of every finite Galois group is fixed by `Φ`
of the idempotent `R ≫ η` of the derived normalized trace `R`, provided the orders of the finite
Galois groups are invertible on the target of `φ`. -/
theorem map_derivedTrace_comp_unit_comp {𝒜 : Type*} [Category 𝒜] [Preadditive 𝒜]
    (Φ : DerivedCategory
      (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ⥤ 𝒜)
    [Φ.Additive] (hΦ : IsColimit ((DerivedCategory.Q ⋙ Φ).mapCocone (T.complexCocone Λ K)))
    {W : 𝒜} (hW : ∀ j, IsIso (Fintype.card (T.Γ j) • 𝟙 W))
    (φ : Φ.obj (R((ginf)_*⟦Λ⟧).obj (L((ginf)^*⟦Λ⟧).obj C)) ⟶ W) {κ : Type*}
    (σ : κ → (Yinf ⟶ Yinf)) (hσ : ∀ k, σ k ≫ ginf = ginf)
    (hσj : ∀ j a, ∃ k, σ k ≫ T.π j = T.π j ≫ T.ρ j a)
    (hφ : ∀ k, Φ.map (derivedUnitTransport Λ (σ k) (hσ k) (hσ k) C) ≫ φ = φ) :
    Φ.map (T.derivedTrace Λ hd K hc a hK C e ≫
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ ginf).unit.app C) ≫ φ = φ := by
  have key := map_comp_eq_of_isColimit_mapCocone (DerivedCategory.Q ⋙ Φ)
    (T.complexCocone Λ K) hΦ (T.complexTrace Λ hd K hc ≫
      ((CondensedRing.upperStarLowerStarAdjunction Λ ginf).mapHomologicalComplex _).unit.app K)
    (fun k ↦ (NatTrans.mapHomologicalComplex (unitTransport Λ (σ k) (hσ k) (hσ k)) _).app K)
    (T.complexNormTraceUnit Λ hd K)
    (fun j a ↦ (NatTrans.mapHomologicalComplex (T.levelAction Λ j a) _).app K)
    (fun j ↦ HomologicalComplex.hom_ext _ _ fun n ↦
      T.infTransport_comp_trace_comp_infUnit Λ hd (K.X n) (hc n) j)
    (fun j ↦ HomologicalComplex.hom_ext _ _ fun n ↦ by
      rw [HomologicalComplex.nsmul_f_apply]
      exact (T.card_smul_normTrace_comp_levelUnit Λ hd (K.X n) j).trans
        ((HomologicalComplex.eval _ (ComplexShape.up ℤ) n).map_sum
          (fun a ↦ (NatTrans.mapHomologicalComplex (T.levelAction Λ j a) _).app K)
          Finset.univ).symm)
    (fun j b ↦ by
      obtain ⟨k, hk⟩ := hσj j b
      refine ⟨k, HomologicalComplex.hom_ext _ _ fun n ↦ ?_⟩
      have h := T.infTransport_comp_infAction Λ (K.X n) (σ k) (hσ k) j b hk
      rw [infAction_eq] at h
      exact h.symm)
    hW (Φ.map (derivedTraceIso Λ K a hK C e).hom ≫ φ) (fun k ↦ by
      rw [Functor.comp_map, ← Functor.map_comp_assoc,
        ← derivedTraceIso_hom_comp_derivedUnitTransport Λ K a hK C e (σ k) (hσ k),
        Functor.map_comp, Category.assoc, hφ])
  rw [← cancel_epi (Φ.map (derivedTraceIso Λ K a hK C e).hom), ← Functor.map_comp_assoc,
    T.derivedTraceIso_hom_comp_derivedTrace_comp_unit Λ hd K hc a hK C e, Φ.map_comp,
    Category.assoc]
  exact key

end AlgebraicGeometry.ProEtale.GaloisTower

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

-- Reuse tensor existence proofs while elaborating composites of derived functors.
private theorem projector_hasTensor₄ObjExt (S : Scheme.{u})
    (R : Sheaf (ProEt.topology S) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    ∀ P Q R₁ S₁ : GradedObject ℤ (Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) R),
      GradedObject.HasTensor₄ObjExt P Q R₁ S₁ := by
  infer_instance

private theorem projector_hasGoodTensor₁₂Tensor (S : Scheme.{u})
    (R : Sheaf (ProEt.topology S) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    ∀ P Q R₁ : GradedObject ℤ (Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) R),
      GradedObject.HasGoodTensor₁₂Tensor P Q R₁ := by
  infer_instance

private theorem projector_hasGoodTensorTensor₂₃ (S : Scheme.{u})
    (R : Sheaf (ProEt.topology S) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    ∀ P Q R₁ : GradedObject ℤ (Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) R),
      GradedObject.HasGoodTensorTensor₂₃ P Q R₁ := by
  infer_instance

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' : Scheme.{u}} (N : NearbyCyclesModel X X') {L : Type u} [Field L]
  (h : N.generic ⟶ Spec (.of L)) (Ω : Type u) [Field Ω] [Algebra L Ω]

/-- Factor the Galois layer exchange through the image of the derived unit. -/
private lemma pullbackExchange_galoisLayerHom_projector_factorization
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    ((N.galoisLayerHom h Ω).pullbackExchange Λ).app C =
      ((leftDerivedUpperStarId Λ X').app ((N.nearbyCycles Λ).obj C)).hom ≫
        (R((N.j)_*⟦Λ⟧) ⋙ L((N.i)^*⟦Λ⟧)).map
          ((derivedUpperStarLowerStarAdjunction Λ
            (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app
              (L((N.ε)^*⟦Λ⟧).obj C)) ≫ (N.galoisLayerExchangeIso h Ω Λ C).hom := by
  have := projector_hasTensor₄ObjExt N.total (condensedRingObj Λ N.total)
  have := projector_hasGoodTensor₁₂Tensor N.total (condensedRingObj Λ N.total)
  have := projector_hasGoodTensorTensor₂₃ N.total (condensedRingObj Λ N.total)
  have hα := Hom.pullbackExchange_app_of_total_eq_id Λ N
    (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))) _ rfl
    (N.galoisLayerHom h Ω) rfl rfl C
  simp only [eqToHom_refl, Category.id_comp] at hα
  rw [Functor.map_comp] at hα
  dsimp only [Functor.comp_map, galoisLayerExchangeIso, Functor.mapIso, Iso.trans,
    Iso.symm, Iso.app]
  exact hα

/-- Express the retraction and its projector using shared exchange and action maps. -/
private theorem exists_galoisLayer_retraction_projector
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (R : R((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))_*⟦Λ⟧).obj
        (L((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))^*⟦Λ⟧).obj
          (L((N.ε)^*⟦Λ⟧).obj C)) ⟶ L((N.ε)^*⟦Λ⟧).obj C)
    (hR : (derivedUpperStarLowerStarAdjunction Λ
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app
        (L((N.ε)^*⟦Λ⟧).obj C) ≫ R = 𝟙 _)
    (hinv : ∀ σ : Ω ≃ₐ[L] Ω, derivedUnitTransport Λ (pullbackAction h _ specGaloisAction_comp σ)
      (pullbackAction_fst h _ specGaloisAction_comp σ)
      (pullbackAction_fst h _ specGaloisAction_comp σ) (L((N.ε)^*⟦Λ⟧).obj C) ≫ R = R) :
    let α := ((N.galoisLayerHom h Ω).pullbackExchange Λ).app C
    let ρ := fun σ ↦ N.galoisLayerAction Λ h Ω σ (L((𝟙 X)^*⟦Λ⟧).obj C)
    let κ := N.galoisLayerExchangeIso h Ω Λ C
    ∃ r, α ≫ r = 𝟙 _ ∧
      (∀ σ, ρ σ ≫ (r ≫ α) = r ≫ α ∧ (r ≫ α) ≫ ρ σ = r ≫ α) ∧
      r ≫ α = κ.inv ≫ (R((N.j)_*⟦Λ⟧) ⋙ L((N.i)^*⟦Λ⟧)).map
        (R ≫ (derivedUpperStarLowerStarAdjunction Λ
          (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app
            (L((N.ε)^*⟦Λ⟧).obj C)) ≫ κ.hom := by
  dsimp only
  have key := exists_invariant_retraction_of_conjugate_eq (R((N.j)_*⟦Λ⟧) ⋙ L((N.i)^*⟦Λ⟧))
    (((N.galoisLayerHom h Ω).pullbackExchange Λ).app C) R _ hR
    ((leftDerivedUpperStarId Λ X').app ((N.nearbyCycles Λ).obj C))
    (N.galoisLayerExchangeIso h Ω Λ C)
    (pullbackExchange_galoisLayerHom_projector_factorization Λ N h Ω C) _ hinv
    (fun σ ↦ N.galoisLayerAction Λ h Ω σ (L((𝟙 X)^*⟦Λ⟧).obj C))
    (fun σ ↦ pullbackExchange_galoisLayerHom_app_comp_galoisLayerAction Λ N h Ω σ C)
    (fun σ ↦ galoisLayerAut_autAction Λ N h Ω σ C)
  exact key

/-- `NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_of_invariant`, with the
idempotent made explicit: `r ≫ α = κ⁻¹ ≫ Li^* Rj_* (R ≫ η) ≫ κ` for the derived unit `η` and
`κ = NearbyCyclesModel.galoisLayerExchangeIso`. -/
theorem exists_retraction_pullbackExchange_galoisLayerHom_of_invariant_eq
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (R : R((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))_*⟦Λ⟧).obj
        (L((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))^*⟦Λ⟧).obj
          (L((N.ε)^*⟦Λ⟧).obj C)) ⟶ L((N.ε)^*⟦Λ⟧).obj C)
    (hR : (derivedUpperStarLowerStarAdjunction Λ
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app
        (L((N.ε)^*⟦Λ⟧).obj C) ≫ R = 𝟙 _)
    (hinv : ∀ σ : Ω ≃ₐ[L] Ω, derivedUnitTransport Λ (pullbackAction h _ specGaloisAction_comp σ)
      (pullbackAction_fst h _ specGaloisAction_comp σ)
      (pullbackAction_fst h _ specGaloisAction_comp σ) (L((N.ε)^*⟦Λ⟧).obj C) ≫ R = R) :
    ∃ r, ((N.galoisLayerHom h Ω).pullbackExchange Λ).app C ≫ r = 𝟙 _ ∧
      (∀ σ : Ω ≃ₐ[L] Ω,
        N.galoisLayerAction Λ h Ω σ (L((𝟙 X)^*⟦Λ⟧).obj C) ≫
            (r ≫ ((N.galoisLayerHom h Ω).pullbackExchange Λ).app C) =
          r ≫ ((N.galoisLayerHom h Ω).pullbackExchange Λ).app C ∧
        (r ≫ ((N.galoisLayerHom h Ω).pullbackExchange Λ).app C) ≫
            N.galoisLayerAction Λ h Ω σ (L((𝟙 X)^*⟦Λ⟧).obj C) =
          r ≫ ((N.galoisLayerHom h Ω).pullbackExchange Λ).app C) ∧
      r ≫ ((N.galoisLayerHom h Ω).pullbackExchange Λ).app C =
        (N.galoisLayerExchangeIso h Ω Λ C).inv ≫
          L((N.i)^*⟦Λ⟧).map (R((N.j)_*⟦Λ⟧).map (R ≫ (derivedUpperStarLowerStarAdjunction Λ
            (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app
              (L((N.ε)^*⟦Λ⟧).obj C))) ≫
          (N.galoisLayerExchangeIso h Ω Λ C).hom := by
  exact exists_galoisLayer_retraction_projector Λ N h Ω C R hR hinv

/-- Transport the tower projector through the Galois layer exchange and an additive functor. -/
private lemma map_galoisLayer_derivedTrace_projector [IsGalois L Ω]
    (hd : ∀ (j : FiniteGaloisIntermediateField L Ω)
      (M : Mod (Sheaf (ProEt.topology N.generic) Ab.{u + 1}) (condensedRingObj Λ N.generic)),
      IsIso (Fintype.card ((galoisTower Ω h).Γ j) • 𝟙 M))
    (C : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (K : CochainComplex
      (Mod (Sheaf (ProEt.topology N.generic) Ab.{u + 1}) (condensedRingObj Λ N.generic)) ℤ)
    (hc : ∀ n, IsColimit ((galoisTower Ω h).moduleCocone Λ (K.X n)))
    (a : ℤ) [K.IsStrictlyGE a]
    (hK : let g := pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))
      ∀ n, ((g)_*⟦Λ⟧).rightAcyclic (((g)^*⟦Λ⟧).obj (K.X n)))
    (e : DerivedCategory.Q.obj K ≅ L((N.ε)^*⟦Λ⟧).obj C)
    {𝒜 : Type*} [Category 𝒜] [Preadditive 𝒜]
    (H : DerivedCategory (Mod (Sheaf (ProEt.topology X') Ab.{u + 1})
      (condensedRingObj Λ X')) ⥤ 𝒜) [H.Additive]
    (hΦ : IsColimit ((DerivedCategory.Q ⋙ R((N.j)_*⟦Λ⟧) ⋙ L((N.i)^*⟦Λ⟧) ⋙ H).mapCocone
      ((galoisTower Ω h).complexCocone Λ K)))
    {W : 𝒜} (hW : ∀ j, IsIso (Fintype.card ((galoisTower Ω h).Γ j) • 𝟙 W))
    (φ : H.obj (((N.galoisLayer h Ω).nearbyCycles Λ).obj (L((𝟙 X)^*⟦Λ⟧).obj C)) ⟶ W)
    {κ : Type*} (S : κ → (Ω ≃ₐ[L] Ω))
    (hS : ∀ (L' : FiniteGaloisIntermediateField L Ω) (b : L' ≃ₐ[L] L'),
      ∃ k, ∀ x : L', S k x = b x)
    (hφ : ∀ k, H.map (N.galoisLayerAction Λ h Ω (S k) (L((𝟙 X)^*⟦Λ⟧).obj C)) ≫ φ = φ) :
    let R := (galoisTower Ω h).derivedTrace Λ hd K hc a hK _ e
    let eLayer := N.galoisLayerExchangeIso h Ω Λ C
    H.map (eLayer.inv ≫ (R((N.j)_*⟦Λ⟧) ⋙ L((N.i)^*⟦Λ⟧)).map
      (R ≫ (derivedUpperStarLowerStarAdjunction Λ
        (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app
          (L((N.ε)^*⟦Λ⟧).obj C)) ≫ eLayer.hom) ≫ φ = φ := by
  dsimp only
  have hσj (j : FiniteGaloisIntermediateField L Ω) (b : j ≃ₐ[L] j) :
      ∃ k, pullbackAction h _ specGaloisAction_comp (S k) ≫ (galoisTower Ω h).π j =
        (galoisTower Ω h).π j ≫ (galoisTower Ω h).ρ j b := by
    obtain ⟨k, hk⟩ := hS j b
    refine ⟨k, ?_⟩
    have hb : (S k).restrictNormal j = b := AlgEquiv.ext fun x ↦
      (algebraMap j Ω).injective ((AlgEquiv.restrictNormal_commutes (S k) j x).trans (hk x))
    rw [← hb]
    exact pullbackAction_comp_galoisLevelProjection h j (S k)
  let eLayer := N.galoisLayerExchangeIso h Ω Λ C
  have hφ' (k : κ) := hφ k
  simp only [galoisLayerAction, galoisLayerAut_autAction] at hφ'
  have key := (galoisTower Ω h).map_derivedTrace_comp_unit_comp Λ hd K hc a hK _ e
    (R((N.j)_*⟦Λ⟧) ⋙ L((N.i)^*⟦Λ⟧) ⋙ H) hΦ hW (H.map eLayer.hom ≫ φ)
    (fun k ↦ pullbackAction h _ specGaloisAction_comp (S k))
    (fun k ↦ pullbackAction_fst h _ specGaloisAction_comp (S k)) hσj
    (fun k ↦ (map_map_conj_comp_eq_iff (𝟭 _) H eLayer _ φ).1 (hφ' k))
  exact (map_map_conj_comp_eq_iff (𝟭 _) H eLayer _ φ).2 key

variable (T₀ : Type) [TopologicalSpace T₀] [CommRing T₀] [IsTopologicalRing T₀]
  [DiscreteTopology T₀] [Finite T₀] [IsGalois L Ω]

/-- **Continuity of nearby cycles along the finite Galois layers, after pullback** to `Z` along
`f' : Z ⟶ X'`: `NearbyCyclesModel.nonempty_isColimit_homology_nearbyCycles_galoisTower`
composed with the derived pullback `Lf'^*`, which commutes with cohomology and preserves
colimits. -/
theorem nonempty_isColimit_homology_leftDerivedUpperStar_nearbyCycles_galoisTower
    [QuasiCompact N.j] [QuasiSeparated N.j]
    (K : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) N.generic)) ℤ)
    (a : ℤ) [K.IsStrictlyGE a]
    (hK : ∀ n, (comparisonUpperStar AddCommGrpCat.{u + 1} N.generic).essImage (K.X n).X)
    {Z : Scheme.{u}} (f' : Z ⟶ X') (q : ℤ) :
    Nonempty (IsColimit ((DerivedCategory.Q ⋙ R((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧) ⋙
      L((N.i)^*⟦Profinite.continuousMapRingObj T₀⟧) ⋙
      L((f')^*⟦Profinite.continuousMapRingObj T₀⟧) ⋙
      DerivedCategory.homologyFunctor _ q).mapCocone
        ((galoisTower Ω h).complexCocone (Profinite.continuousMapRingObj T₀) K))) := by
  obtain ⟨hc⟩ := N.nonempty_isColimit_homology_nearbyCycles_galoisTower T₀ h Ω K a hK q
  have hc' := isColimitOfPreserves ((f')^*⟦Profinite.continuousMapRingObj T₀⟧) hc
  exact ⟨IsColimit.mapCoconeEquiv (Functor.isoWhiskerLeft
    (DerivedCategory.Q ⋙ R((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧) ⋙
      L((N.i)^*⟦Profinite.continuousMapRingObj T₀⟧))
    (homologyLeftDerivedUpperStarIso f' (Profinite.continuousMapRingObj T₀) q).symm) hc'⟩

/-- Construct the projector using a bounded complex of étale origin. The exchange and action
are shared in the conclusion, so their derived functors are elaborated only once. -/
private theorem exists_retraction_galoisLayer_projector_of_complex
    [QuasiCompact N.j] [QuasiSeparated N.j]
    (hp : ∀ L' : FiniteGaloisIntermediateField L Ω, IsUnit ((Module.finrank L L' : ℕ) : T₀))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) X)))
    (K : CochainComplex (Mod (Sheaf (ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) N.generic)) ℤ)
    (a : ℤ) [K.IsStrictlyGE a]
    (hterms : ∀ n, ∃ F₀ : Sheaf N.generic.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} T₀)),
      Nonempty ((finiteCoefficientModEquivalence N.generic T₀).functor.obj (K.X n) ≅
        (ν^*(N.generic)[ModuleCat.{u + 1} (ULift.{u + 1} T₀)]).obj F₀))
    (e : DerivedCategory.Q.obj K ≅ L((N.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C) :
    let Λ₀ := Profinite.continuousMapRingObj T₀
    let α := ((N.galoisLayerHom h Ω).pullbackExchange Λ₀).app C
    let D := ((N.galoisLayer h Ω).nearbyCycles Λ₀).obj (L((𝟙 X)^*⟦Λ₀⟧).obj C)
    let ρ := fun σ ↦ N.galoisLayerAction Λ₀ h Ω σ (L((𝟙 X)^*⟦Λ₀⟧).obj C)
    ∃ r, α ≫ r = 𝟙 _ ∧
      (∀ σ, ρ σ ≫ (r ≫ α) = r ≫ α ∧ (r ≫ α) ≫ ρ σ = r ≫ α) ∧
      ∀ {Z : Scheme.{u}} (f' : Z ⟶ X') (q : ℤ),
        let H := L((f')^*⟦Λ₀⟧) ⋙ DerivedCategory.homologyFunctor _ q
        ∀ {W : Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ₀ Z)}
          (φ : H.obj D ⟶ W) {κ : Type*} (S : κ → (Ω ≃ₐ[L] Ω)),
          (∀ (L' : FiniteGaloisIntermediateField L Ω) (a : L' ≃ₐ[L] L'),
            ∃ k, ∀ x : L', S k x = a x) →
          (∀ k, H.map (ρ (S k)) ≫ φ = φ) → H.map (r ≫ α) ≫ φ = φ := by
  intro Λ₀ α D ρ
  choose F₀ hF₀ using hterms
  have hW (j : FiniteGaloisIntermediateField L Ω) {Y : Scheme.{u}}
      (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj T₀) Y)) :
      IsIso (Fintype.card ((galoisTower Ω h).Γ j) • 𝟙 M) := by
    have hcard : Fintype.card ((galoisTower Ω h).Γ j) = Module.finrank L j := by
      rw [← Nat.card_eq_fintype_card]
      exact IsGalois.card_aut_eq_finrank L j
    rw [hcard]
    exact isIso_nsmul_id_mod_of_isUnit _ (Profinite.continuousMapConstRingHom T₀) (hp j) M
  have hKe (n : ℤ) := essImage_comparisonUpperStar_X T₀ (K.X n) (F₀ n) (hF₀ n).some
  have hc (n : ℤ) := isColimitModuleCocone_galoisTower Ω h T₀ (K.X n) (hKe n)
  have hK (n : ℤ) :=
    rightAcyclic_condensedRingLowerStar_upperStar_of_iso (Ω := Ω) T₀ h (K.X n) (F₀ n) (hF₀ n)
  let R := (galoisTower Ω h).derivedTrace _ (fun j M ↦ hW j M) K hc a hK _ e
  have hR := (galoisTower Ω h).unit_app_comp_derivedTrace _ (fun j M ↦ hW j M) K hc a hK _ e
  have hinv (σ : Ω ≃ₐ[L] Ω) :=
    (galoisTower Ω h).derivedUnitTransport_comp_derivedTrace _ (fun j M ↦ hW j M)
      K hc a hK _ e _ (pullbackAction_fst h _ specGaloisAction_comp σ)
      (fun (j : FiniteGaloisIntermediateField L Ω) ↦
        ⟨σ.restrictNormal j, pullbackAction_comp_galoisLevelProjection h j σ⟩)
  have hret := exists_galoisLayer_retraction_projector (Profinite.continuousMapRingObj T₀)
    N h Ω C R hR hinv
  -- Rebuilding the other conjuncts repeats large definitional equality checks.
  refine hret.imp fun r ↦ And.imp_right (And.imp_right ?_)
  intro hr₃ Z f' q H W φ κ S hS hφ
  obtain ⟨hΦ⟩ := nonempty_isColimit_homology_leftDerivedUpperStar_nearbyCycles_galoisTower N h Ω T₀
    K a hKe f' q
  rw [hr₃]
  exact map_galoisLayer_derivedTrace_projector (Profinite.continuousMapRingObj T₀) N h Ω
    (fun j M ↦ hW j M) C K hc a hK e
    H hΦ (fun j ↦ hW j W) φ S hS hφ

/-- Use a complex of étale origin to construct the projector. -/
private theorem exists_retraction_galoisLayer_projector_of_etaleOrigin
    [QuasiCompact N.j] [QuasiSeparated N.j]
    (hp : ∀ L' : FiniteGaloisIntermediateField L Ω, IsUnit ((Module.finrank L L' : ℕ) : T₀))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) X)))
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic T₀).functor.obj
        (L((N.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C))) :
    let Λ₀ := Profinite.continuousMapRingObj T₀
    let α := ((N.galoisLayerHom h Ω).pullbackExchange Λ₀).app C
    let D := ((N.galoisLayer h Ω).nearbyCycles Λ₀).obj (L((𝟙 X)^*⟦Λ₀⟧).obj C)
    let ρ := fun σ ↦ N.galoisLayerAction Λ₀ h Ω σ (L((𝟙 X)^*⟦Λ₀⟧).obj C)
    ∃ r, α ≫ r = 𝟙 _ ∧
      (∀ σ, ρ σ ≫ (r ≫ α) = r ≫ α ∧ (r ≫ α) ≫ ρ σ = r ≫ α) ∧
      ∀ {Z : Scheme.{u}} (f' : Z ⟶ X') (q : ℤ),
        let H := L((f')^*⟦Λ₀⟧) ⋙ DerivedCategory.homologyFunctor _ q
        ∀ {W : Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ₀ Z)}
          (φ : H.obj D ⟶ W) {κ : Type*} (S : κ → (Ω ≃ₐ[L] Ω)),
          (∀ (L' : FiniteGaloisIntermediateField L Ω) (a : L' ≃ₐ[L] L'),
            ∃ k, ∀ x : L', S k x = a x) →
          (∀ k, H.map (ρ (S k)) ≫ φ = φ) → H.map (r ≫ α) ≫ φ = φ := by
  have hcomplex := exists_complex_of_plusEtaleOrigin (X := N.generic) T₀
    (L((N.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C) hC
  obtain ⟨K, a, hKa, hterms, ⟨e⟩⟩ := hcomplex
  exact exists_retraction_galoisLayer_projector_of_complex N h Ω T₀ hp C K a hterms e

/-- **The nearby cycles of `N` are the `Gal(Ω/L)`-invariants of those of the Galois layer `N_Ω`,
with a projector onto all the invariants** (torsion coefficients in which the degrees of the
finite Galois subextensions of `Ω/L` are invertible). If `Lε^* C` is bounded below of étale
origin, the pullback exchange `α : L(𝟙)^* Ψ_N C ⟶ Ψ_{N_Ω} (L(𝟙)^* C)` of the projection
`N_Ω ⟶ N` has a retraction `r` whose idempotent `r ≫ α` is fixed by the action of every
`σ ∈ Gal(Ω/L)` on both sides, and is the projector onto all the invariants on cohomology sheaves:
for `f' : Z ⟶ X'`, every map out of `Hᵠ(Lf'^* Ψ_{N_Ω} (L(𝟙)^* C))` which is invariant under a
family `S k` of elements of `Gal(Ω/L)` restricting onto every `Gal(L'/L)` is fixed by
`Hᵠ(Lf'^* (r ≫ α))`. -/
theorem exists_retraction_pullbackExchange_galoisLayerHom_of_plusEtaleOrigin_projector
    [QuasiCompact N.j] [QuasiSeparated N.j]
    (hp : ∀ L' : FiniteGaloisIntermediateField L Ω, IsUnit ((Module.finrank L L' : ℕ) : T₀))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) X)))
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic T₀).functor.obj
        (L((N.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C))) :
    ∃ r, ((N.galoisLayerHom h Ω).pullbackExchange (Profinite.continuousMapRingObj T₀)).app C ≫
        r = 𝟙 _ ∧
      (∀ σ : Ω ≃ₐ[L] Ω,
        N.galoisLayerAction (Profinite.continuousMapRingObj T₀) h Ω σ
            (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C) ≫
            (r ≫ ((N.galoisLayerHom h Ω).pullbackExchange
              (Profinite.continuousMapRingObj T₀)).app C) =
          r ≫ ((N.galoisLayerHom h Ω).pullbackExchange (Profinite.continuousMapRingObj T₀)).app C ∧
        (r ≫ ((N.galoisLayerHom h Ω).pullbackExchange (Profinite.continuousMapRingObj T₀)).app C) ≫
            N.galoisLayerAction (Profinite.continuousMapRingObj T₀) h Ω σ
              (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C) =
          r ≫ ((N.galoisLayerHom h Ω).pullbackExchange
            (Profinite.continuousMapRingObj T₀)).app C) ∧
      ∀ {Z : Scheme.{u}} (f' : Z ⟶ X') (q : ℤ)
        {W : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj T₀) Z)}
        (φ : (DerivedCategory.homologyFunctor _ q).obj
          (L((f')^*⟦Profinite.continuousMapRingObj T₀⟧).obj
            (((N.galoisLayer h Ω).nearbyCycles (Profinite.continuousMapRingObj T₀)).obj
              (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C))) ⟶ W)
        {κ : Type*} (S : κ → (Ω ≃ₐ[L] Ω)),
        (∀ (L' : FiniteGaloisIntermediateField L Ω) (a : L' ≃ₐ[L] L'),
          ∃ k, ∀ x : L', S k x = a x) →
        (∀ k, (DerivedCategory.homologyFunctor _ q).map
          (L((f')^*⟦Profinite.continuousMapRingObj T₀⟧).map
            (N.galoisLayerAction (Profinite.continuousMapRingObj T₀) h Ω (S k)
              (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C))) ≫ φ = φ) →
        (DerivedCategory.homologyFunctor _ q).map
          (L((f')^*⟦Profinite.continuousMapRingObj T₀⟧).map
            (r ≫ ((N.galoisLayerHom h Ω).pullbackExchange
              (Profinite.continuousMapRingObj T₀)).app C)) ≫ φ = φ := by
  exact exists_retraction_galoisLayer_projector_of_etaleOrigin N h Ω T₀ hp C hC

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
