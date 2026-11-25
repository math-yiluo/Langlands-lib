/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisInvariantsProjector
public import WeilConjectures.Mathlib.CategoryTheory.Subobject.NoetherianObject

/-!

# Continuity of the Galois action on noetherian cohomology sheaves of nearby cycles

Let `N` be a model of `X` with special fibre `X'` and `j : N.generic ⟶ N.total` quasi-compact and
quasi-separated, `h : N.generic ⟶ Spec L`, `Ω/L` a Galois extension, `T₀` a finite discrete ring
and `Λ = C(-, T₀)`. Let `C` be such that `Lε^* C` is bounded below of étale origin.

If the cohomology sheaf `Hᵠ(Ψ_{N_Ω} C)` of the nearby cycles of the Galois layer is a noetherian
object, then an open subgroup of `Gal(Ω/L)` acts trivially on it: there is a finite Galois
subextension `L'` such that every `σ` fixing `L'` pointwise acts as the identity
(`NearbyCyclesModel.exists_forall_homology_galoisLayerAction_eq_id`), and similarly for finitely
many degrees at once
(`NearbyCyclesModel.exists_forall_mem_finset_homology_galoisLayerAction_eq_id`).

Indeed by continuity (`NearbyCyclesModel.nonempty_isColimit_homology_nearbyCycles_galoisTower`)
`Hᵠ(Ψ_{N_Ω} C)` is the filtered colimit of the cohomology sheaves of the finite layers; since it is
noetherian, the colimit is attained at some level `L'`
(`CategoryTheory.exists_epi_ι_of_isNoetherianObject`), on which `σ` acts through its restriction
to `L'`, i.e. trivially.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

/-- Cancel after applying functors, then transport the equality along an isomorphism. -/
private lemma map_eq_of_epi_of_intertwining
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (Q : C ⥤ D) (F : D ⥤ E) {A B : C} {Z : D}
    (i : A ⟶ B) [hi : Epi ((Q ⋙ F).map i)] (e : Q.obj B ≅ Z)
    {u v : B ⟶ B} {x y : Z ⟶ Z} (huv : i ≫ u = i ≫ v)
    (hx : e.hom ≫ x = Q.map u ≫ e.hom) (hy : e.hom ≫ y = Q.map v ≫ e.hom) :
    F.map x = F.map y := by
  have h : (Q ⋙ F).map u = (Q ⋙ F).map v := by
    apply (cancel_epi ((Q ⋙ F).map i)).1
    simpa only [Functor.map_comp] using congrArg (Q ⋙ F).map huv
  apply (cancel_epi (F.map e.hom)).1
  rw [← F.map_comp, ← F.map_comp, hx, hy, F.map_comp, F.map_comp]
  exact congrArg (fun f ↦ f ≫ F.map e.hom) h

namespace AlgebraicGeometry.ProEtale.GaloisTower

open Scheme CondensedRing

variable {X Yinf : Scheme.{u}} {ginf : Yinf ⟶ X} [WeaklyEtale ginf] (T : GaloisTower ginf)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (K : CochainComplex
    (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)

/-- The coprojections of the cocone of complexes `g_{j*} g_j^* K ⟶ g_{∞*} g_∞^* K` intertwine the
unit transport along an automorphism `σ` of `Y_∞` over `X` covering `a ∈ Γ_j` with the action
of `a` at the level `j`. -/
lemma complexCocone_ι_app_comp_unitTransport (σ : Yinf ⟶ Yinf) (hσ : σ ≫ ginf = ginf) (j : T.J)
    (a : T.Γ j) (ha : σ ≫ T.π j = T.π j ≫ T.ρ j a) :
    (T.complexCocone Λ K).ι.app j ≫
        (NatTrans.mapHomologicalComplex (unitTransport Λ σ hσ hσ) _).app K =
      (NatTrans.mapHomologicalComplex (T.levelAction Λ j a) _).app K ≫
        (T.complexCocone Λ K).ι.app j :=
  HomologicalComplex.hom_ext _ _ fun n ↦ by
    have h := T.infTransport_comp_infAction Λ (K.X n) σ hσ j a ha
    rw [infAction_eq] at h
    exact h

end AlgebraicGeometry.ProEtale.GaloisTower

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {X X' : Scheme.{u}} (N : NearbyCyclesModel X X') {L : Type u} [Field L]
  (h : N.generic ⟶ Spec (.of L)) (Ω : Type u) [Field Ω] [Algebra L Ω] [IsGalois L Ω]
  (T₀ : Type) [TopologicalSpace T₀] [CommRing T₀] [IsTopologicalRing T₀]
  [DiscreteTopology T₀] [Finite T₀]

omit [IsGalois L Ω] in
/-- An automorphism of `Ω` fixing `L'` pointwise restricts to the identity of `L'`. -/
lemma restrictNormal_eq_one_of_forall_apply_eq (L' : FiniteGaloisIntermediateField L Ω)
    (σ : Ω ≃ₐ[L] Ω) (hσ : ∀ x : L', σ x = x) : σ.restrictNormal L' = 1 :=
  AlgEquiv.ext fun x ↦
    (algebraMap L' Ω).injective ((AlgEquiv.restrictNormal_commutes σ L' x).trans (hσ x))

/-- **Continuity of the Galois action on a noetherian cohomology sheaf of nearby cycles**
(torsion coefficients). If `Lε^* C` is bounded below of étale origin and `Hᵠ(Ψ_{N_Ω} C)` is a
noetherian object, there is a finite Galois subextension `L'` of `Ω/L` such that every
`σ ∈ Gal(Ω/L)` fixing `L'` pointwise acts trivially on `Hᵠ(Ψ_{N_Ω} C)`. -/
theorem exists_forall_homology_galoisLayerAction_eq_id [QuasiCompact N.j] [QuasiSeparated N.j]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) X)))
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic T₀).functor.obj
        (L((N.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)))
    (q : ℤ) [IsNoetherianObject ((DerivedCategory.homologyFunctor _ q).obj
      (((N.galoisLayer h Ω).nearbyCycles (Profinite.continuousMapRingObj T₀)).obj
        (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)))] :
    ∃ L' : FiniteGaloisIntermediateField L Ω, ∀ σ : Ω ≃ₐ[L] Ω, (∀ x : L', σ x = x) →
      (DerivedCategory.homologyFunctor _ q).map
        (N.galoisLayerAction (Profinite.continuousMapRingObj T₀) h Ω σ
          (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)) = 𝟙 _ := by
  obtain ⟨K, a, hKa, hterms, ⟨e⟩⟩ := exists_complex_of_plusEtaleOrigin T₀ _ hC
  choose F₀ hF₀ using hterms
  have hKe (n : ℤ) := essImage_comparisonUpperStar_X T₀ (K.X n) (F₀ n) (hF₀ n).some
  have hK (n : ℤ) :=
    rightAcyclic_condensedRingLowerStar_upperStar_of_iso (Ω := Ω) T₀ h (K.X n) (F₀ n) (hF₀ n)
  obtain ⟨hΦ⟩ := N.nonempty_isColimit_homology_nearbyCycles_galoisTower T₀ h Ω K a hKe q
  let H := DerivedCategory.homologyFunctor
    (Mod (Sheaf (Scheme.ProEt.topology X') Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) X')) q
  let Ψ := R((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧) ⋙
    L((N.i)^*⟦Profinite.continuousMapRingObj T₀⟧) ⋙ H
  let Φ := DerivedCategory.Q ⋙ Ψ
  let eK := GaloisTower.derivedTraceIso (Profinite.continuousMapRingObj T₀) K a hK _ e
  let κ := N.galoisLayerExchangeIso h Ω (Profinite.continuousMapRingObj T₀) C
  have : IsNoetherianObject (Φ.mapCocone
      ((galoisTower Ω h).complexCocone (Profinite.continuousMapRingObj T₀) K)).pt :=
    isNoetherianObject_of_mono (Ψ.map eK.hom ≫ H.map κ.hom)
  obtain ⟨j, hj⟩ := exists_epi_ι_of_isNoetherianObject hΦ
  let L' : FiniteGaloisIntermediateField L Ω := j
  refine ⟨L', fun σ hσ ↦ ?_⟩
  have hU (τ : Ω ≃ₐ[L] Ω) (hτ : ∀ x : L', τ x = x) :=
    (galoisTower Ω h).complexCocone_ι_app_comp_unitTransport _ K _
      (pullbackAction_fst h _ specGaloisAction_comp τ) j 1
      (restrictNormal_eq_one_of_forall_apply_eq Ω L' τ hτ ▸
        pullbackAction_comp_galoisLevelProjection h L' τ)
  have he (τ : Ω ≃ₐ[L] Ω) :=
    GaloisTower.derivedTraceIso_hom_comp_derivedUnitTransport
      (Profinite.continuousMapRingObj T₀) K a hK _ e
      (pullbackAction h _ specGaloisAction_comp τ)
      (pullbackAction_fst h _ specGaloisAction_comp τ)
  have hA := map_eq_of_epi_of_intertwining (hi := hj) DerivedCategory.Q Ψ
    (((galoisTower Ω h).complexCocone (Profinite.continuousMapRingObj T₀) K).ι.app j) eK
    ((hU σ hσ).trans (hU 1 fun _ ↦ rfl).symm) (he σ) (he 1)
  have hact (τ : Ω ≃ₐ[L] Ω) := congrArg H.map
    (galoisLayerAut_autAction (Profinite.continuousMapRingObj T₀) N h Ω τ C)
  simp only [H.map_comp] at hact
  exact (hact σ).trans ((congrArg (fun f ↦ H.map κ.inv ≫ f ≫ H.map κ.hom) hA).trans
    ((hact 1).symm.trans ((congrArg H.map
      (N.galoisLayerAction_one (Profinite.continuousMapRingObj T₀) h Ω _)).trans (H.map_id _))))

/-- **Continuity of the Galois action on noetherian cohomology sheaves of nearby cycles**, for
finitely many degrees at once: if the `Hᵠ(Ψ_{N_Ω} C)` are noetherian for `q ∈ s`, there is a single
finite Galois subextension `L'` such that every `σ` fixing `L'` pointwise acts trivially on all of
them. -/
theorem exists_forall_mem_finset_homology_galoisLayerAction_eq_id [QuasiCompact N.j]
    [QuasiSeparated N.j]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) X)))
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic T₀).functor.obj
        (L((N.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)))
    (s : Finset ℤ) (hs : ∀ q ∈ s, IsNoetherianObject ((DerivedCategory.homologyFunctor _ q).obj
      (((N.galoisLayer h Ω).nearbyCycles (Profinite.continuousMapRingObj T₀)).obj
        (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)))) :
    ∃ L' : FiniteGaloisIntermediateField L Ω, ∀ q ∈ s, ∀ σ : Ω ≃ₐ[L] Ω, (∀ x : L', σ x = x) →
      (DerivedCategory.homologyFunctor _ q).map
        (N.galoisLayerAction (Profinite.continuousMapRingObj T₀) h Ω σ
          (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)) = 𝟙 _ := by
  choose L' hL' using fun (q : ℤ) (hq : q ∈ s) ↦
    have := hs q hq
    N.exists_forall_homology_galoisLayerAction_eq_id h Ω T₀ C hC q
  refine ⟨s.attach.sup fun q ↦ L' q.1 q.2, fun q hq σ hσ ↦ hL' q hq σ fun x ↦
    hσ ⟨x, Finset.le_sup (f := fun q : s ↦ L' q.1 q.2) (s.mem_attach ⟨q, hq⟩) x.2⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
