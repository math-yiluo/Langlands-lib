/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisInvariantsCoinvariant
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomologyTensorColimit
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.LeftTExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeIntegralRational

/-!

# The projector onto the invariants of nearby cycles, after a tensor product

Let `N` be a model, `h : N.generic ⟶ Spec L`, `Ω/L` Galois with degrees invertible in a finite
discrete field `T₀`, `Λ = C(-, T₀)` and `C` with `Lε^* C` bounded below of étale origin. The
exchange `α : Ψ_N C ⟶ Ψ_{N_Ω} C` of the Galois layer has a retraction `r` whose projector
`r ≫ α` is the projector onto all the invariants in the following form: after pullback along any
`f' : Z ⟶ X'` and tensor product with any bounded below `W`, every map out of
`Hᵠ(Lf'^* Ψ_{N_Ω} C ⊗ W)` invariant under the Galois action (on the first factor) is fixed by
`Hᵠ(Lf'^*(r ≫ α) ⊗ W)`
(`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_coinvariant_tensor`).

This is the coinvariant property used for the projection formula `(E ⊗ B)^P = E^P ⊗ B` in the
generic-slicing step of Gabber's Künneth formula (blueprint `prose-E-10`,
`NearbyCyclesModel.isIso_kunnethMap_of_isIso_galoisLayer`). The proof is that of
`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_coinvariant`, with the
continuity of the cohomology sheaves of the tensor product along the finite layers
(`ProEtale.CondensedRing.isColimit_homology_tensorRight_mapCocone`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

/-- Transport a split unit and its coinvariant property along a functor and two isomorphisms. -/
private lemma tensor_coinvariant_retraction_of_conjugate
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

private lemma tensor_coinvariant_unit_retraction_of_iso (a : ℤ) [K.IsStrictlyGE a]
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

omit [IsGalois L Ω] in
private lemma tensor_coinvariant_exchange_factorization
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
private lemma tensor_coinvariant_pullbackExchange_of_unit
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
  exact CategoryTheory.tensor_coinvariant_retraction_of_conjugate
    (R((N.j)_*⟦Λ⟧) ⋙ L((N.i)^*⟦Λ⟧)) G _ R
    ((leftDerivedUpperStarId Λ X').app ((N.nearbyCycles Λ).obj C))
    (N.galoisLayerExchangeIso h Ω Λ C) _
    (tensor_coinvariant_exchange_factorization N h Ω Λ C) hR
    (fun k ↦ derivedUnitTransport Λ
      (pullbackAction h _ specGaloisAction_comp (act k))
      (pullbackAction_fst h _ specGaloisAction_comp (act k))
      (pullbackAction_fst h _ specGaloisAction_comp (act k))
      (L((N.ε)^*⟦Λ⟧).obj C))
    (fun k ↦ N.galoisLayerAction Λ h Ω (act k) (L((𝟙 X)^*⟦Λ⟧).obj C))
    (fun k ↦ galoisLayerAut_autAction Λ N h Ω (act k) C)

/-- **`Ψ_N` is the summand of all the invariants of `Ψ_{N_Ω}`, after a continuous functor**
(SGA 4½, [Th. finitude], Lemme 3.4; torsion coefficients). Let `Ω/L` be Galois with degrees
invertible in `T₀` and `C` bounded below of étale origin on the generic fibre. The pullback
exchange `α : Ψ_N C ⟶ Ψ_{N_Ω} C` of the Galois layer has a retraction `r` such that, for every
additive functor `G` to module objects which carries the cocone of the finite layers of every
bounded below complex (after `Li^* Rj_*`) to a colimit, every map out of `G(Ψ_{N_Ω} C)` invariant
under a family `act` of elements of `Gal(Ω/L)` meeting every element of every finite quotient
`Gal(L'/L)` is fixed by `G(r ≫ α)`. For `G = Hᵠ ∘ Lf'^*` this is
`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_coinvariant`. -/
theorem exists_retraction_pullbackExchange_galoisLayerHom_coinvariant_of_isColimit
    [QuasiCompact N.j] [QuasiSeparated N.j]
    (hp : ∀ L' : FiniteGaloisIntermediateField L Ω, IsUnit ((Module.finrank L L' : ℕ) : T₀))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) X)))
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic T₀).functor.obj
        (L((N.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)))
    {κ : Type*} (act : κ → (Ω ≃ₐ[L] Ω))
    (hact : ∀ (L' : FiniteGaloisIntermediateField L Ω) (a : L' ≃ₐ[L] L'),
      ∃ k, ∀ x : L', act k x = a x) :
    ∃ r, ((N.galoisLayerHom h Ω).pullbackExchange (Profinite.continuousMapRingObj T₀)).app C ≫
        r = 𝟙 _ ∧
      ∀ {Z : Scheme.{u}} (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X') Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj T₀) X')) ⥤
            Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
              (condensedRingObj (Profinite.continuousMapRingObj T₀) Z)) [G.Additive],
        (∀ (K : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
            (condensedRingObj (Profinite.continuousMapRingObj T₀) N.generic)) ℤ) (a : ℤ)
            [K.IsStrictlyGE a], (∀ n, IsColimit ((galoisTower Ω h).abCocone (K.X n).X)) →
          Nonempty (IsColimit ((DerivedCategory.Q ⋙
            R((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧) ⋙
              L((N.i)^*⟦Profinite.continuousMapRingObj T₀⟧) ⋙ G).mapCocone
                ((galoisTower Ω h).complexCocone (Profinite.continuousMapRingObj T₀) K)))) →
        ∀ {W : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj T₀) Z)}
        (φ : G.obj (((N.galoisLayer h Ω).nearbyCycles (Profinite.continuousMapRingObj T₀)).obj
              (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)) ⟶ W),
        (∀ k, G.map (N.galoisLayerAction (Profinite.continuousMapRingObj T₀) h Ω (act k)
              (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)) ≫ φ = φ) →
        G.map (r ≫ ((N.galoisLayerHom h Ω).pullbackExchange
              (Profinite.continuousMapRingObj T₀)).app C) ≫ φ = φ := by
  refine (exists_complex_of_plusEtaleOrigin T₀ _ hC).elim fun K hK ↦ ?_
  refine hK.elim fun a ha ↦ ?_
  have hKa : K.IsStrictlyGE a := ha.1
  have hterms := ha.2.1
  refine ha.2.2.elim fun e ↦ ?_
  choose F₀ hF₀ using hterms
  have hd : ∀ (j : FiniteGaloisIntermediateField L Ω)
      (M : Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj T₀) N.generic)),
      IsIso (Fintype.card ((galoisTower Ω h).Γ j) • 𝟙 M) := fun j M ↦ by
    have hc : Fintype.card ((galoisTower Ω h).Γ j) = Module.finrank L j := by
      change Fintype.card (j ≃ₐ[L] j) = _
      rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
    rw [hc]
    exact CondensedRing.isIso_nsmul_id_mod_of_isUnit _ (Profinite.continuousMapConstRingHom T₀)
      (hp j) M
  have hc := fun n ↦ isColimitModuleCocone_galoisTower Ω h T₀ (K.X n)
    (essImage_comparisonUpperStar_X T₀ (K.X n) (F₀ n) (hF₀ n).some)
  have hcab := fun n ↦ (nonempty_isColimit_galoisUpperLowerCocone (Ω := Ω) h (K.X n).X
    (essImage_comparisonUpperStar_X T₀ (K.X n) (F₀ n) (hF₀ n).some)).some
  have hK := fun n ↦
    rightAcyclic_condensedRingLowerStar_upperStar_of_iso (Ω := Ω) T₀ h (K.X n) (F₀ n) (hF₀ n)
  have hlift : ∀ (j : FiniteGaloisIntermediateField L Ω) (b : (galoisTower Ω h).Γ j), ∃ k,
      pullbackAction h _ specGaloisAction_comp (act k) ≫ (galoisTower Ω h).π j =
        (galoisTower Ω h).π j ≫ (galoisTower Ω h).ρ j b := fun j b ↦ by
    obtain ⟨k, hk⟩ := hact j b
    refine ⟨k, ?_⟩
    have hres : (act k).restrictNormal j = b := by
      ext x
      exact (AlgEquiv.restrictNormal_commutes (act k) (j : IntermediateField L Ω) x).trans (hk x)
    have := pullbackAction_comp_galoisLevelProjection h j (act k)
    rw [hres] at this
    exact this
  have hRC := (galoisTower Ω h).tensor_coinvariant_unit_retraction_of_iso
    (Profinite.continuousMapRingObj T₀) hd K hc a hK _ e
  have hmain := fun {Z : Scheme.{u}}
      (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X') Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj T₀) X')) ⥤
          Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
            (condensedRingObj (Profinite.continuousMapRingObj T₀) Z)) ↦
    tensor_coinvariant_pullbackExchange_of_unit N h Ω
      (Profinite.continuousMapRingObj T₀) C _ hRC act G
  refine ⟨_, (hmain (DerivedCategory.homologyFunctor _ 0)).1, fun {Z} G _ hG W φ hφ ↦ ?_⟩
  have hdZ : ∀ (j : FiniteGaloisIntermediateField L Ω)
      (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj T₀) Z)),
      IsIso (Fintype.card ((galoisTower Ω h).Γ j) • 𝟙 M) := fun j M ↦ by
    have hc : Fintype.card ((galoisTower Ω h).Γ j) = Module.finrank L j := by
      change Fintype.card (j ≃ₐ[L] j) = _
      rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
    rw [hc]
    exact CondensedRing.isIso_nsmul_id_mod_of_isUnit _ (Profinite.continuousMapConstRingHom T₀)
      (hp j) M
  refine (hmain G).2 φ (fun φ' hφ' ↦ ?_) hφ
  exact (galoisTower Ω h).map_derivedUnitRetraction_comp_unit_comp_eq_of_invariant_of_iso
    (Profinite.continuousMapRingObj T₀) hd K hc a hK _ e
    (R((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧) ⋙
      L((N.i)^*⟦Profinite.continuousMapRingObj T₀⟧) ⋙ G)
    (hG K a hcab).some
    (fun k ↦ pullbackAction h _ specGaloisAction_comp (act k))
    (fun k ↦ pullbackAction_fst h _ specGaloisAction_comp (act k)) hlift (fun j ↦ hdZ j W) φ'
    hφ'

/-- Tensoring a Galois tower with a bounded below complex preserves its homology colimits. -/
private lemma tensor_coinvariant_isColimit (T₀ : Type)
    [TopologicalSpace T₀] [Field T₀] [IsTopologicalRing T₀] [DiscreteTopology T₀] [Finite T₀]
    [QuasiCompact N.j] [QuasiSeparated N.j]
    {Yinf : Scheme.{u}} {ginf : Yinf ⟶ N.generic} [WeaklyEtale ginf] (T : GaloisTower ginf)
    (K : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) N.generic)) ℤ)
    (a : ℤ) [K.IsStrictlyGE a] (hcab : ∀ n, IsColimit (T.abCocone (K.X n).X))
    {Z : Scheme.{u}} (f' : Z ⟶ X')
    (V : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) Z)))
    (b : ℤ) (hV : V.IsGE b) (q : ℤ) :
    Nonempty (IsColimit ((DerivedCategory.Q ⋙ R((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧) ⋙
      L((N.i)^*⟦Profinite.continuousMapRingObj T₀⟧) ⋙
        L((f')^*⟦Profinite.continuousMapRingObj T₀⟧) ⋙ tensorRight V ⋙
          DerivedCategory.homologyFunctor _ q).mapCocone
            (T.complexCocone (Profinite.continuousMapRingObj T₀) K))) := by
  -- the cohomology of the tensor product is continuous along the finite layers
  let F := DerivedCategory.Q ⋙ R((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧) ⋙
    L((N.i)^*⟦Profinite.continuousMapRingObj T₀⟧) ⋙ L((f')^*⟦Profinite.continuousMapRingObj T₀⟧)
  have hGE : ∀ (Y : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) N.generic)) ℤ), Y.IsStrictlyGE a →
        (F.obj Y).IsGE a := fun Y hY ↦ by
    have := Functor.isGE_rightDerivedFunctor_obj ((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧)
      (DerivedCategory.Q.obj Y) a
    have := isGE_leftDerivedUpperStar_obj (Profinite.continuousMapRingObj T₀) N.i
      (R((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧).obj (DerivedCategory.Q.obj Y)) a
    exact isGE_leftDerivedUpperStar_obj (Profinite.continuousMapRingObj T₀) f' _ a
  have hpt : (T.complexCocone (Profinite.continuousMapRingObj T₀) K).pt.IsStrictlyGE
      a := (CochainComplex.isStrictlyGE_iff _ a).2 fun i hi ↦
    (ProEtale.GaloisTower.infFunctor (Profinite.continuousMapRingObj T₀) _).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE K a i hi)
  exact isColimit_homology_tensorRight_mapCocone' T₀
    (T.complexCocone (Profinite.continuousMapRingObj T₀) K) F a
    (fun j ↦ hGE _ inferInstance) (hGE _ hpt)
    (fun p ↦ (nonempty_isColimit_homology_pullback_nearbyCycles_complexCocone T₀ N
      T K hcab a f' p).some) V b hV q

/-- A projector with the coinvariant property for continuous functors has that property
on the homology of its pullback tensored with a bounded below complex. -/
private lemma tensor_coinvariant_property (T₀ : Type)
    [TopologicalSpace T₀] [Field T₀] [IsTopologicalRing T₀] [DiscreteTopology T₀] [Finite T₀]
    [QuasiCompact N.j] [QuasiSeparated N.j]
    {Yinf : Scheme.{u}} {ginf : Yinf ⟶ N.generic} [WeaklyEtale ginf] (T : GaloisTower ginf)
    {Z : Scheme.{u}} (f' : Z ⟶ X')
    {Y : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X') Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) X'))}
    (p : Y ⟶ Y) {κ : Type*} (act : κ → (Y ⟶ Y))
    (hcoinv : ∀ (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X') Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj T₀) X')) ⥤
            Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
              (condensedRingObj (Profinite.continuousMapRingObj T₀) Z)) [G.Additive],
        (∀ (K : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
            (condensedRingObj (Profinite.continuousMapRingObj T₀) N.generic)) ℤ) (a : ℤ)
            [K.IsStrictlyGE a], (∀ n, IsColimit (T.abCocone (K.X n).X)) →
          Nonempty (IsColimit ((DerivedCategory.Q ⋙
            R((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧) ⋙
              L((N.i)^*⟦Profinite.continuousMapRingObj T₀⟧) ⋙ G).mapCocone
                (T.complexCocone (Profinite.continuousMapRingObj T₀) K)))) →
        ∀ {W : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj T₀) Z)} (φ : G.obj Y ⟶ W),
        (∀ k, G.map (act k) ≫ φ = φ) → G.map p ≫ φ = φ) :
    ∀ (q : ℤ) (V : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj T₀) Z))) (b : ℤ), V.IsGE b →
        ∀ {W : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj T₀) Z)}
        (φ : (DerivedCategory.homologyFunctor _ q).obj
          (L((f')^*⟦Profinite.continuousMapRingObj T₀⟧).obj Y ⊗ V) ⟶ W),
        (∀ k, (DerivedCategory.homologyFunctor _ q).map
          (L((f')^*⟦Profinite.continuousMapRingObj T₀⟧).map (act k) ▷ V) ≫ φ = φ) →
        (DerivedCategory.homologyFunctor _ q).map
          (L((f')^*⟦Profinite.continuousMapRingObj T₀⟧).map p ▷ V) ≫ φ = φ := by
  intro q V b hV W φ hφ
  exact hcoinv (L((f')^*⟦Profinite.continuousMapRingObj T₀⟧) ⋙ tensorRight V ⋙
    DerivedCategory.homologyFunctor _ q)
    (fun K a _ hcab ↦ tensor_coinvariant_isColimit N T₀ T K a hcab f' V b hV q) φ hφ

/-- **`Ψ_N` is the summand of all the invariants of `Ψ_{N_Ω}`, after a tensor product** (SGA 4½,
[Th. finitude], Lemme 3.4; blueprint `prose-E-10`; finite field coefficients).
Let `Ω/L` be Galois with degrees invertible in the finite field `T₀` and `C` bounded below of étale
origin on the generic fibre. The pullback exchange `α : Ψ_N C ⟶ Ψ_{N_Ω} C` of the Galois layer has
a retraction `r` such that, on the cohomology sheaves of `Lf'^*(-) ⊗ V` for any `f' : Z ⟶ X'` and
any bounded below `V`, every map invariant under a family `act` of elements of `Gal(Ω/L)` meeting
every element of every finite quotient `Gal(L'/L)` is fixed by the projector `r ≫ α`. -/
theorem exists_retraction_pullbackExchange_galoisLayerHom_coinvariant_tensor (T₀ : Type)
    [TopologicalSpace T₀] [Field T₀] [IsTopologicalRing T₀] [DiscreteTopology T₀] [Finite T₀]
    [QuasiCompact N.j] [QuasiSeparated N.j]
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
      ∀ (q : ℤ) (V : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj T₀) Z))) (b : ℤ), V.IsGE b →
        ∀ {W : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj T₀) Z)}
        (φ : (DerivedCategory.homologyFunctor _ q).obj
          (L((f')^*⟦Profinite.continuousMapRingObj T₀⟧).obj
            (((N.galoisLayer h Ω).nearbyCycles (Profinite.continuousMapRingObj T₀)).obj
              (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)) ⊗ V) ⟶ W),
        (∀ k, (DerivedCategory.homologyFunctor _ q).map
          (L((f')^*⟦Profinite.continuousMapRingObj T₀⟧).map
            (N.galoisLayerAction (Profinite.continuousMapRingObj T₀) h Ω (act k)
              (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)) ▷ V) ≫ φ = φ) →
        (DerivedCategory.homologyFunctor _ q).map
          (L((f')^*⟦Profinite.continuousMapRingObj T₀⟧).map
            (r ≫ ((N.galoisLayerHom h Ω).pullbackExchange
              (Profinite.continuousMapRingObj T₀)).app C) ▷ V) ≫ φ = φ :=
  (exists_retraction_pullbackExchange_galoisLayerHom_coinvariant_of_isColimit
    T₀ N h Ω hp C hC act hact).imp fun _ hr ↦
      ⟨hr.1, tensor_coinvariant_property N T₀ (galoisTower Ω h) f' _ _ (hr.2 (Z := Z))⟩

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
