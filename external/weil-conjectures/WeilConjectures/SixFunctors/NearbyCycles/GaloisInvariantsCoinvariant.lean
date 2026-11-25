/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Retract
public import WeilConjectures.SixFunctors.NearbyCycles.GaloisContinuity
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.TowerAverage

/-!

# The invariant summand of nearby cycles is the summand of all invariants

Let `N` be a model, `h : N.generic ⟶ Spec L`, `Ω/L` Galois with degrees invertible in a finite
ring `T₀`, and `Λ = C(-, T₀)`. PR #1818 (SGA 4½, [Th. finitude], Lemme 3.4) shows that the
exchange `α : Ψ_N ⟶ Ψ_{N_Ω}` of the Galois layer is split by a retraction `r` whose projector
`r ≫ α` is Galois invariant. This file shows that the projector is the projector onto *all* the
invariants, on cohomology sheaves: every map out of `Hᵠ(Lf'^* Ψ_{N_Ω})` which is invariant under
the Galois action is fixed by `Hᵠ(Lf'^*(r ≫ α))`
(`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_coinvariant`). This is the
content of `Ψ_N = (Ψ_{N_Ω})^P` beyond the existence of an invariant summand, and the input needed
to compare the invariant summands under a change of trait
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_galoisLayerMap`).

The proof is a continuity argument. The retraction is induced by the levelwise normalized trace
of the Galois tower of `Ω/L`, which on the image of a finite level `L'` is the average over
`Gal(L'/L)` (`GaloisTower.map_complexTrace_comp_unit_comp_eq_of_invariant`), and the cohomology
sheaves of the pulled back nearby cycles of the tower are the filtered colimits of those of the
finite levels
(`NearbyCyclesModel.nonempty_isColimit_homology_pullback_nearbyCycles_complexCocone`). A map out
of such a colimit which is invariant under the Galois action is fixed by every average, hence by
the projector. This argument is carried out on cohomology sheaves: in the derived category the
colimit is only a homotopy colimit.

## Main results

- `GaloisTower.map_derivedUnitRetraction_comp_unit_comp_eq_of_invariant`: the derived version,
  after any additive functor carrying the cocone of the finite levels to a colimit.
- `NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_coinvariant`: the nearby
  cycles statement.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

/-- Transport a split unit and its coinvariant property along a functor and two isomorphisms. -/
private lemma coinvariant_retraction_of_conjugate
    {C D A : Type*} [Category C] [Category D] [Category A] (F : C ⥤ D) (G : D ⥤ A)
    {S T : C} {P Q : D} (η : S ⟶ T) (R : T ⟶ S) (i : P ≅ F.obj S) (e : F.obj T ≅ Q)
    (α : P ⟶ Q) (hα : α = i.hom ≫ F.map η ≫ e.hom) (hR : η ≫ R = 𝟙 S)
    {κ : Type*} (u : κ → (T ⟶ T)) (ρ : κ → (Q ⟶ Q))
    (hρ : ∀ k, ρ k = e.inv ≫ F.map (u k) ≫ e.hom) :
    let r := e.inv ≫ F.map R ≫ i.inv
    α ≫ r = 𝟙 P ∧
      ∀ {W : A} (φ : G.obj Q ⟶ W),
        (∀ φ' : G.obj (F.obj T) ⟶ W,
          (∀ k, G.map (F.map (u k)) ≫ φ' = φ') →
            G.map (F.map (R ≫ η)) ≫ φ' = φ') →
        (∀ k, G.map (ρ k) ≫ φ = φ) → G.map (r ≫ α) ≫ φ = φ := by
  dsimp only
  have he : (e.inv ≫ F.map R ≫ i.inv) ≫ α = e.inv ≫ F.map (R ≫ η) ≫ e.hom := by
    rw [hα]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, F.map_comp]
  refine ⟨?_, ?_⟩
  · rw [hα]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← F.map_comp_assoc, hR, F.map_id, Category.id_comp, i.hom_inv_id]
  · intro W φ hco hφ
    have key := hco (G.map e.hom ≫ φ) fun k ↦ by
      have h := hφ k
      rw [hρ k, G.map_comp, G.map_comp] at h
      simp only [Category.assoc] at h
      calc
        _ = G.map e.hom ≫
            (G.map e.inv ≫ G.map (F.map (u k)) ≫ G.map e.hom ≫ φ) := by
          rw [← G.map_comp_assoc e.hom e.inv, e.hom_inv_id, G.map_id, Category.id_comp]
        _ = _ := by rw [h]
    rw [he, G.map_comp, G.map_comp, Category.assoc, Category.assoc, key,
      ← G.map_comp_assoc, e.inv_hom_id, G.map_id, Category.id_comp]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (T₀ : Type) [TopologicalSpace T₀] [CommRing T₀] [IsTopologicalRing T₀]
  [DiscreteTopology T₀] [Finite T₀]
  {X X' : Scheme.{u}} (N : NearbyCyclesModel X X')

/-- **Continuity of the pulled back nearby cycles along a Galois tower.** For a Galois tower `T`
over the generic fibre of `N` and a bounded below complex `K` whose terms have
`g_{∞*} g_∞^* Kⁿ` the colimit of the finite levels, the cohomology sheaves of
`Lf'^* Li^* Rj_* (g_{∞*} g_∞^* K)` are the filtered colimits of those of the finite levels, for
any `f' : Z ⟶ X'`. -/
theorem nonempty_isColimit_homology_pullback_nearbyCycles_complexCocone [QuasiCompact N.j]
    [QuasiSeparated N.j] {Yinf : Scheme.{u}} {ginf : Yinf ⟶ N.generic} [WeaklyEtale ginf]
    (T : GaloisTower ginf)
    (K : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) N.generic)) ℤ)
    (hc : ∀ n, IsColimit (T.abCocone (K.X n).X)) (a : ℤ) [K.IsStrictlyGE a]
    {Z : Scheme.{u}} (f' : Z ⟶ X') (q : ℤ) :
    Nonempty (IsColimit ((DerivedCategory.Q ⋙ R((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧) ⋙
      L((N.i)^*⟦Profinite.continuousMapRingObj T₀⟧) ⋙
        L((f')^*⟦Profinite.continuousMapRingObj T₀⟧) ⋙
          DerivedCategory.homologyFunctor _ q).mapCocone
            (T.complexCocone (Profinite.continuousMapRingObj T₀) K))) := by
  obtain ⟨hc⟩ := T.isColimit_homology_rightDerivedLowerStar_complexCocone T₀ K hc a N.j q
  have hc₁ := isColimitOfPreserves ((N.i)^*⟦Profinite.continuousMapRingObj T₀⟧) hc
  have hc₂ := IsColimit.mapCoconeEquiv (Functor.isoWhiskerLeft
    (DerivedCategory.Q ⋙ R((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧))
    (homologyLeftDerivedUpperStarIso N.i (Profinite.continuousMapRingObj T₀) q).symm) hc₁
  have hc₃ := isColimitOfPreserves ((f')^*⟦Profinite.continuousMapRingObj T₀⟧) hc₂
  exact ⟨IsColimit.mapCoconeEquiv (Functor.isoWhiskerLeft
    (DerivedCategory.Q ⋙ R((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧) ⋙
      L((N.i)^*⟦Profinite.continuousMapRingObj T₀⟧))
    (homologyLeftDerivedUpperStarIso f' (Profinite.continuousMapRingObj T₀) q).symm) hc₃⟩

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

namespace AlgebraicGeometry.ProEtale.GaloisTower

open Scheme CondensedRing

variable {X Yinf : Scheme.{u}} {ginf : Yinf ⟶ X} [WeaklyEtale ginf] (T : GaloisTower ginf)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (hd : ∀ (j : T.J)
    (N : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      IsIso (Fintype.card (T.Γ j) • 𝟙 N))
  (K : CochainComplex
    (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
  (hc : ∀ n, IsColimit (T.moduleCocone Λ (K.X n)))

private lemma map_iso_inv_comp_map_eq_of_map_comp_eq
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y : C} (i : X ≅ Y) {t : X ⟶ X} {Z : D} (φ : F.obj Y ⟶ Z)
    (h : F.map t ≫ F.map i.hom ≫ φ = F.map i.hom ≫ φ) :
    F.map (i.inv ≫ t ≫ i.hom) ≫ φ = φ := by
  rw [F.map_comp, F.map_comp, Category.assoc, Category.assoc, h,
    ← F.map_comp_assoc, i.inv_hom_id, F.map_id, Category.id_comp]

/-- **The derived trace projector is the projector onto the invariants, after any continuous
additive functor.** Let `R` be the retraction of the derived unit `K ⟶ Rg_{∞*} Lg_∞^* K` induced by
the levelwise normalized traces (`Adjunction.derivedUnitRetraction`), and `G` an additive functor
such that `Q ⋙ G` carries the cocone of the finite levels `g_{j*} g_j^* K ⟶ g_{∞*} g_∞^* K` to a
colimit. Then every map `φ : G(Rg_{∞*} Lg_∞^* K) ⟶ W` invariant under the derived unit transports
along a family of automorphisms covering all the finite Galois groups is fixed by `G(R ≫ η)`. -/
theorem map_derivedUnitRetraction_comp_unit_comp_eq_of_invariant (a : ℤ) [K.IsStrictlyGE a]
    (hK : ∀ n, ((ginf)_*⟦Λ⟧).rightAcyclic (((ginf)^*⟦Λ⟧).obj (K.X n))) {A : Type*} [Category A]
    [Preadditive A]
    (G : DerivedCategory (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ⥤ A) [G.Additive]
    (hG : IsColimit ((DerivedCategory.Q ⋙ G).mapCocone (T.complexCocone Λ K)))
    {ι : Type*} (act : ι → (Yinf ⟶ Yinf)) (hact : ∀ i, act i ≫ ginf = ginf)
    (hlift : ∀ j a, ∃ i, act i ≫ T.π j = T.π j ≫ T.ρ j a) {W : A}
    (hW : ∀ j, IsIso (Fintype.card (T.Γ j) • 𝟙 W))
    (φ : G.obj (R((ginf)_*⟦Λ⟧).obj (L((ginf)^*⟦Λ⟧).obj (DerivedCategory.Q.obj K))) ⟶ W)
    (hφ : ∀ i, G.map (derivedUnitTransport Λ (act i) (hact i) (hact i)
      (DerivedCategory.Q.obj K)) ≫ φ = φ) :
    G.map (Adjunction.derivedUnitRetraction K a hK (T.complexTrace Λ hd K hc) ≫
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ ginf).unit.app
        (DerivedCategory.Q.obj K)) ≫ φ = φ := by
  have hR := Adjunction.derivedUnitRetraction_comp_derivedAdjunction_unit_app K a hK
    (T.complexTrace Λ hd K hc) (CondensedRing.upperStarLowerStarAdjunction Λ ginf)
  rw [show CondensedRing.derivedUpperStarLowerStarAdjunction Λ ginf =
    (CondensedRing.upperStarLowerStarAdjunction Λ ginf).derivedAdjunction from rfl, hR]
  let D := Adjunction.derivedUnitIso (f := (ginf)^*⟦Λ⟧) (g := (ginf)_*⟦Λ⟧) K a hK
  have key := T.map_complexTrace_comp_unit_comp_eq_of_invariant Λ hd K hc
    (DerivedCategory.Q ⋙ G) hG act hact hlift hW (G.map D.hom ≫ φ) fun i ↦ by
      have h := derivedUnitIso_hom_comp_derivedUnitTransport_self Λ ginf (act i) (hact i) K a hK
      rw [Functor.comp_map, ← Category.assoc, ← G.map_comp, ← h, G.map_comp, Category.assoc,
        hφ i]
  rw [Functor.comp_map] at key
  exact map_iso_inv_comp_map_eq_of_map_comp_eq G D φ key

/-- `GaloisTower.map_derivedUnitRetraction_comp_unit_comp_eq_of_invariant` for an object `C ≅ K`
of the derived category, with the transported retraction
`Rg_{∞*} Lg_∞^* e⁻¹ ≫ R ≫ e`
(as in `GaloisTower.exists_invariant_retraction_derivedUnit_of_iso`). -/
theorem map_derivedUnitRetraction_comp_unit_comp_eq_of_invariant_of_iso (a : ℤ)
    [K.IsStrictlyGE a] (hK : ∀ n, ((ginf)_*⟦Λ⟧).rightAcyclic (((ginf)^*⟦Λ⟧).obj (K.X n)))
    (C : DerivedCategory
      (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (e : DerivedCategory.Q.obj K ≅ C) {A : Type*} [Category A] [Preadditive A]
    (G : DerivedCategory (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ⥤ A) [G.Additive]
    (hG : IsColimit ((DerivedCategory.Q ⋙ G).mapCocone (T.complexCocone Λ K)))
    {ι : Type*} (act : ι → (Yinf ⟶ Yinf)) (hact : ∀ i, act i ≫ ginf = ginf)
    (hlift : ∀ j a, ∃ i, act i ≫ T.π j = T.π j ≫ T.ρ j a) {W : A}
    (hW : ∀ j, IsIso (Fintype.card (T.Γ j) • 𝟙 W))
    (φ : G.obj (R((ginf)_*⟦Λ⟧).obj (L((ginf)^*⟦Λ⟧).obj C)) ⟶ W)
    (hφ : ∀ i, G.map (derivedUnitTransport Λ (act i) (hact i) (hact i) C) ≫ φ = φ) :
    G.map ((R((ginf)_*⟦Λ⟧).map (L((ginf)^*⟦Λ⟧).map e.inv) ≫
        Adjunction.derivedUnitRetraction K a hK (T.complexTrace Λ hd K hc) ≫ e.hom) ≫
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ ginf).unit.app C) ≫ φ = φ := by
  have hn := (CondensedRing.derivedUpperStarLowerStarAdjunction Λ ginf).unit.naturality e.hom
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at hn
  have key := T.map_derivedUnitRetraction_comp_unit_comp_eq_of_invariant Λ hd K hc a hK G hG act
    hact hlift hW (G.map (R((ginf)_*⟦Λ⟧).map (L((ginf)^*⟦Λ⟧).map e.hom)) ≫ φ) fun i ↦ by
      have h := derivedUnitTransport_naturality Λ (act i) (hact i) (hact i) e.hom
      rw [← G.map_comp_assoc]
      exact (congrArg (fun x ↦ G.map x ≫ φ) h).symm.trans (by rw [G.map_comp_assoc, hφ i])
  have h : (R((ginf)_*⟦Λ⟧).map (L((ginf)^*⟦Λ⟧).map e.inv) ≫
      Adjunction.derivedUnitRetraction K a hK (T.complexTrace Λ hd K hc) ≫ e.hom) ≫
        (CondensedRing.derivedUpperStarLowerStarAdjunction Λ ginf).unit.app C =
      R((ginf)_*⟦Λ⟧).map (L((ginf)^*⟦Λ⟧).map e.inv) ≫
        (Adjunction.derivedUnitRetraction K a hK (T.complexTrace Λ hd K hc) ≫
          (CondensedRing.derivedUpperStarLowerStarAdjunction Λ ginf).unit.app
            (DerivedCategory.Q.obj K)) ≫ R((ginf)_*⟦Λ⟧).map (L((ginf)^*⟦Λ⟧).map e.hom) := by
    simp only [Category.assoc, hn]
  rw [h]
  exact map_iso_inv_comp_map_eq_of_map_comp_eq G
    (R((ginf)_*⟦Λ⟧).mapIso (L((ginf)^*⟦Λ⟧).mapIso e)) φ key

private lemma unit_comp_derivedRetraction_of_iso (a : ℤ) [K.IsStrictlyGE a]
    (hK : ∀ n, ((ginf)_*⟦Λ⟧).rightAcyclic (((ginf)^*⟦Λ⟧).obj (K.X n)))
    (C : DerivedCategory
      (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (e : DerivedCategory.Q.obj K ≅ C) :
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ ginf).unit.app C ≫
      (R((ginf)_*⟦Λ⟧).map (L((ginf)^*⟦Λ⟧).map e.inv) ≫
        Adjunction.derivedUnitRetraction K a hK (T.complexTrace Λ hd K hc) ≫ e.hom) = 𝟙 C := by
  have hR : (CondensedRing.derivedUpperStarLowerStarAdjunction Λ ginf).unit.app
      (DerivedCategory.Q.obj K) ≫
        Adjunction.derivedUnitRetraction K a hK (T.complexTrace Λ hd K hc) = 𝟙 _ :=
    Adjunction.derivedAdjunction_unit_app_comp_derivedUnitRetraction K a hK _
      (CondensedRing.upperStarLowerStarAdjunction Λ ginf) (T.unit_comp_complexTrace Λ hd K hc)
  have hn := (CondensedRing.derivedUpperStarLowerStarAdjunction Λ ginf).unit.naturality e.inv
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at hn
  rw [← reassoc_of% hn, reassoc_of% hR, e.inv_hom_id]

end AlgebraicGeometry.ProEtale.GaloisTower

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (T₀ : Type) [TopologicalSpace T₀] [CommRing T₀] [IsTopologicalRing T₀]
  [DiscreteTopology T₀] [Finite T₀]
  {X X' : Scheme.{u}} (N : NearbyCyclesModel X X') {L : Type u} [Field L]
  (h : N.generic ⟶ Spec (.of L)) (Ω : Type u) [Field Ω] [Algebra L Ω] [IsGalois L Ω]

omit [DiscreteTopology T₀] [Finite T₀] in
private lemma coinvariant_degree_isIso
    (hp : ∀ L' : FiniteGaloisIntermediateField L Ω, IsUnit ((Module.finrank L L' : ℕ) : T₀))
    (j : FiniteGaloisIntermediateField L Ω) {Z : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) Z)) :
    IsIso (Fintype.card ((galoisTower Ω h).Γ j) • 𝟙 M) := by
  have hc : Fintype.card ((galoisTower Ω h).Γ j) = Module.finrank L j := by
    change Fintype.card (j ≃ₐ[L] j) = _
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  rw [hc]
  exact CondensedRing.isIso_nsmul_id_mod_of_isUnit _ (Profinite.continuousMapConstRingHom T₀)
    (hp j) M

private lemma coinvariant_action_lift {κ : Type*} (act : κ → (Ω ≃ₐ[L] Ω))
    (hact : ∀ (L' : FiniteGaloisIntermediateField L Ω) (a : L' ≃ₐ[L] L'),
      ∃ k, ∀ x : L', act k x = a x) (j : FiniteGaloisIntermediateField L Ω)
    (b : (galoisTower Ω h).Γ j) :
    ∃ k, pullbackAction h _ specGaloisAction_comp (act k) ≫ (galoisTower Ω h).π j =
      (galoisTower Ω h).π j ≫ (galoisTower Ω h).ρ j b := by
  obtain ⟨k, hk⟩ := hact j b
  refine ⟨k, ?_⟩
  have hres : (act k).restrictNormal j = b := by
    ext x
    exact (AlgEquiv.restrictNormal_commutes (act k) (j : IntermediateField L Ω) x).trans (hk x)
  have h := pullbackAction_comp_galoisLevelProjection h j (act k)
  rw [hres] at h
  exact h

omit [IsGalois L Ω] in
private lemma galoisLayerExchange_factorization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    ((N.galoisLayerHom h Ω).pullbackExchange Λ).app C =
      ((leftDerivedUpperStarId Λ X').app ((N.nearbyCycles Λ).obj C)).hom ≫
        (R((N.j)_*⟦Λ⟧) ⋙ L((N.i)^*⟦Λ⟧)).map
          ((derivedUpperStarLowerStarAdjunction Λ
            (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app
              (L((N.ε)^*⟦Λ⟧).obj C)) ≫ (N.galoisLayerExchangeIso h Ω Λ C).hom := by
  have hα := Hom.pullbackExchange_app_of_total_eq_id Λ N
    (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))) _ rfl
    (N.galoisLayerHom h Ω) rfl rfl C
  simp only [eqToHom_refl, Category.id_comp] at hα
  rw [Functor.map_comp] at hα
  exact hα

omit [IsGalois L Ω] in
/-- Transport the coinvariant property of a retraction of the derived unit through the
Galois layer exchange isomorphism. The retraction is independent of the functor `G`. -/
private lemma coinvariant_pullbackExchange_of_unit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (R : R((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))_*⟦Λ⟧).obj
      (L((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))^*⟦Λ⟧).obj
        (L((N.ε)^*⟦Λ⟧).obj C)) ⟶
          L((N.ε)^*⟦Λ⟧).obj C)
    (hR : (derivedUpperStarLowerStarAdjunction Λ
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app
        (L((N.ε)^*⟦Λ⟧).obj C) ≫ R = 𝟙 _)
    {κ : Type*} (act : κ → (Ω ≃ₐ[L] Ω)) {A : Type*} [Category A]
    (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X') Ab.{u + 1})
      (condensedRingObj Λ X')) ⥤ A) :
    let F₁ := R((N.j)_*⟦Λ⟧)
    let F₂ := L((N.i)^*⟦Λ⟧)
    let D := L((N.ε)^*⟦Λ⟧).obj C
    let η := (derivedUpperStarLowerStarAdjunction Λ
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app D
    let α := ((N.galoisLayerHom h Ω).pullbackExchange Λ).app C
    let r := (N.galoisLayerExchangeIso h Ω Λ C).inv ≫ F₂.map (F₁.map R) ≫
      ((leftDerivedUpperStarId Λ X').app _).inv
    α ≫ r = 𝟙 _ ∧
      ∀ {W : A} (φ : G.obj (((N.galoisLayer h Ω).nearbyCycles Λ).obj
          (L((𝟙 X)^*⟦Λ⟧).obj C)) ⟶ W),
        (∀ φ' : (F₁ ⋙ F₂ ⋙ G).obj _ ⟶ W,
          (∀ k, (F₁ ⋙ F₂ ⋙ G).map (derivedUnitTransport Λ
            (pullbackAction h _ specGaloisAction_comp (act k))
            (pullbackAction_fst h _ specGaloisAction_comp (act k))
            (pullbackAction_fst h _ specGaloisAction_comp (act k)) D) ≫ φ' = φ') →
          (F₁ ⋙ F₂ ⋙ G).map (R ≫ η) ≫ φ' = φ') →
        (∀ k, G.map (N.galoisLayerAction Λ h Ω (act k)
          (L((𝟙 X)^*⟦Λ⟧).obj C)) ≫ φ = φ) →
        G.map (r ≫ α) ≫ φ = φ := by
  exact CategoryTheory.coinvariant_retraction_of_conjugate
    (R((N.j)_*⟦Λ⟧) ⋙ L((N.i)^*⟦Λ⟧)) G _ R
    ((leftDerivedUpperStarId Λ X').app ((N.nearbyCycles Λ).obj C))
    (N.galoisLayerExchangeIso h Ω Λ C) _ (galoisLayerExchange_factorization N h Ω Λ C) hR
    (fun k ↦ derivedUnitTransport Λ
      (pullbackAction h _ specGaloisAction_comp (act k))
      (pullbackAction_fst h _ specGaloisAction_comp (act k))
      (pullbackAction_fst h _ specGaloisAction_comp (act k))
      (L((N.ε)^*⟦Λ⟧).obj C))
    (fun k ↦ N.galoisLayerAction Λ h Ω (act k) (L((𝟙 X)^*⟦Λ⟧).obj C))
    (fun k ↦ galoisLayerAut_autAction Λ N h Ω (act k) C)

private theorem exists_retraction_pullbackExchange_galoisLayerHom_coinvariant_of_complex
    [QuasiCompact N.j] [QuasiSeparated N.j]
    (hp : ∀ L' : FiniteGaloisIntermediateField L Ω, IsUnit ((Module.finrank L L' : ℕ) : T₀))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) X)))
    (K : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) N.generic)) ℤ)
    (a : ℤ) [K.IsStrictlyGE a]
    (hterms : ∀ n, ∃ F₀ : Sheaf N.generic.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} T₀)),
      Nonempty ((finiteCoefficientModEquivalence N.generic T₀).functor.obj (K.X n) ≅
        (ν^*(N.generic)[ModuleCat.{u + 1} (ULift.{u + 1} T₀)]).obj F₀))
    (e : DerivedCategory.Q.obj K ≅ L((N.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)
    {Z : Scheme.{u}} (f' : Z ⟶ X') {κ : Type*} (act : κ → (Ω ≃ₐ[L] Ω))
    (hact : ∀ (L' : FiniteGaloisIntermediateField L Ω) (a : L' ≃ₐ[L] L'),
      ∃ k, ∀ x : L', act k x = a x) :
    ∃ r, ((N.galoisLayerHom h Ω).pullbackExchange (Profinite.continuousMapRingObj T₀)).app C ≫
        r = 𝟙 _ ∧
      ∀ (q : ℤ) {W : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj T₀) Z)}
        (φ : (DerivedCategory.homologyFunctor _ q).obj
          (L((f')^*⟦Profinite.continuousMapRingObj T₀⟧).obj
            (((N.galoisLayer h Ω).nearbyCycles (Profinite.continuousMapRingObj T₀)).obj
              (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C))) ⟶ W),
        (∀ k, (DerivedCategory.homologyFunctor _ q).map
          (L((f')^*⟦Profinite.continuousMapRingObj T₀⟧).map
            (N.galoisLayerAction (Profinite.continuousMapRingObj T₀) h Ω (act k)
              (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C))) ≫ φ = φ) →
        (DerivedCategory.homologyFunctor _ q).map
          (L((f')^*⟦Profinite.continuousMapRingObj T₀⟧).map
            (r ≫ ((N.galoisLayerHom h Ω).pullbackExchange
              (Profinite.continuousMapRingObj T₀)).app C)) ≫ φ = φ := by
  choose F₀ hF₀ using hterms
  have hd := fun j M ↦ coinvariant_degree_isIso T₀ N h Ω hp j (Z := N.generic) M
  have hdZ := fun j M ↦ coinvariant_degree_isIso T₀ N h Ω hp j (Z := Z) M
  have hc := fun n ↦ isColimitModuleCocone_galoisTower Ω h T₀ (K.X n)
    (essImage_comparisonUpperStar_X T₀ (K.X n) (F₀ n) (hF₀ n).some)
  have hcab := fun n ↦ (nonempty_isColimit_galoisUpperLowerCocone (Ω := Ω) h (K.X n).X
    (essImage_comparisonUpperStar_X T₀ (K.X n) (F₀ n) (hF₀ n).some)).some
  have hK := fun n ↦
    rightAcyclic_condensedRingLowerStar_upperStar_of_iso (Ω := Ω) T₀ h (K.X n) (F₀ n) (hF₀ n)
  have hlift := coinvariant_action_lift N h Ω act hact
  have hRC := (galoisTower Ω h).unit_comp_derivedRetraction_of_iso
    (Profinite.continuousMapRingObj T₀) hd K hc a hK _ e
  have hmain (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X') Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) X')) ⥤
        Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj T₀) Z)) :=
    coinvariant_pullbackExchange_of_unit N h Ω (Profinite.continuousMapRingObj T₀) C _ hRC act G
  refine ⟨_, (hmain (L((f')^*⟦Profinite.continuousMapRingObj T₀⟧) ⋙
    DerivedCategory.homologyFunctor _ 0)).1, fun q W φ hφ ↦ ?_⟩
  refine (hmain (L((f')^*⟦Profinite.continuousMapRingObj T₀⟧) ⋙
    DerivedCategory.homologyFunctor _ q)).2 φ (fun φ' hφ' ↦ ?_) hφ
  exact (galoisTower Ω h).map_derivedUnitRetraction_comp_unit_comp_eq_of_invariant_of_iso
    (Profinite.continuousMapRingObj T₀) hd K hc a hK _ e
    (R((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧) ⋙
      L((N.i)^*⟦Profinite.continuousMapRingObj T₀⟧) ⋙
        L((f')^*⟦Profinite.continuousMapRingObj T₀⟧) ⋙ DerivedCategory.homologyFunctor _ q)
    (nonempty_isColimit_homology_pullback_nearbyCycles_complexCocone T₀ N (galoisTower Ω h) K
      hcab a f' q).some
    (fun k ↦ pullbackAction h _ specGaloisAction_comp (act k))
    (fun k ↦ pullbackAction_fst h _ specGaloisAction_comp (act k)) hlift (fun j ↦ hdZ j W) φ'
    hφ'

/-- **`Ψ_N` is the summand of all the invariants of `Ψ_{N_Ω}`** (SGA 4½, [Th. finitude],
Lemme 3.4; torsion coefficients `Λ = C(-, T₀)`). Let `Ω/L` be Galois with degrees invertible in
`T₀` and `C` bounded below of étale origin on the generic fibre. The pullback exchange
`α : Ψ_N C ⟶ Ψ_{N_Ω} C` of the Galois layer has a retraction `r` such that, on the cohomology
sheaves of the pullback along any `f' : Z ⟶ X'`, every map invariant under a family `act` of
elements of `Gal(Ω/L)` meeting every element of every finite quotient `Gal(L'/L)` is fixed by the
projector `r ≫ α`: the projector `r ≫ α` is the projector onto *all* the invariants. -/
theorem exists_retraction_pullbackExchange_galoisLayerHom_coinvariant [QuasiCompact N.j]
    [QuasiSeparated N.j]
    (hp : ∀ L' : FiniteGaloisIntermediateField L Ω, IsUnit ((Module.finrank L L' : ℕ) : T₀))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) X)))
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic T₀).functor.obj
        (L((N.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)))
    {Z : Scheme.{u}} (f' : Z ⟶ X') {κ : Type*} (act : κ → (Ω ≃ₐ[L] Ω))
    (hact : ∀ (L' : FiniteGaloisIntermediateField L Ω) (a : L' ≃ₐ[L] L'),
      ∃ k, ∀ x : L', act k x = a x) :
    ∃ r, ((N.galoisLayerHom h Ω).pullbackExchange (Profinite.continuousMapRingObj T₀)).app C ≫
        r = 𝟙 _ ∧
      ∀ (q : ℤ) {W : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj T₀) Z)}
        (φ : (DerivedCategory.homologyFunctor _ q).obj
          (L((f')^*⟦Profinite.continuousMapRingObj T₀⟧).obj
            (((N.galoisLayer h Ω).nearbyCycles (Profinite.continuousMapRingObj T₀)).obj
              (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C))) ⟶ W),
        (∀ k, (DerivedCategory.homologyFunctor _ q).map
          (L((f')^*⟦Profinite.continuousMapRingObj T₀⟧).map
            (N.galoisLayerAction (Profinite.continuousMapRingObj T₀) h Ω (act k)
              (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C))) ≫ φ = φ) →
        (DerivedCategory.homologyFunctor _ q).map
          (L((f')^*⟦Profinite.continuousMapRingObj T₀⟧).map
            (r ≫ ((N.galoisLayerHom h Ω).pullbackExchange
              (Profinite.continuousMapRingObj T₀)).app C)) ≫ φ = φ := by
  obtain ⟨K, a, hKa, hterms, ⟨e⟩⟩ := exists_complex_of_plusEtaleOrigin T₀ _ hC
  exact exists_retraction_pullbackExchange_galoisLayerHom_coinvariant_of_complex
    T₀ N h Ω hp C K a hterms e f' act hact

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
