/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.FieldTower
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.MoebiusDecomposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.TowerProjector
public import WeilConjectures.FieldTheory.Galois.FiniteGaloisIntermediateField
public import WeilConjectures.Mathlib.Combinatorics.Enumerative.IncidenceAlgebra

/-!
# The Möbius decomposition of the Galois tower of a field extension

Let `Ω/L` be a Galois extension, `h : G ⟶ Spec L` and `T` the Galois tower of `Ω/L` over `G`
(`AlgebraicGeometry.ProEtale.galoisTower`), with finite levels `G ×_L j` for the finite Galois
subextensions `j` and Galois groups `Gal(j/L)`. Let `M` be a `Λ_G`-module object such that
`M_∞ = g_{∞*} g_∞^* M` is the colimit of the finite levels `M_j`, the orders `|Gal(j/L)|` being
invertible.

For a finite Galois subextension `k`, the images `N j k ≤ Gal(j/L)` of `Gal(Ω/k)` form a compatible
family of normal subgroups (`AlgebraicGeometry.ProEtale.galoisTower_transport_comp_levelAvg`),
whose projector `π_k : M_∞ ⟶ M_∞` (`AlgebraicGeometry.ProEtale.GaloisTower.proj`) is the
projector onto the `Gal(Ω/k)`-invariants. By the Galois correspondence `π_k ≫ π_m = π_(k ⊓ m)`
(`AlgebraicGeometry.ProEtale.galoisTower_proj_comp_proj`); moreover `π_j` is the identity on the
image of the level `j`, `π_⊥ = τ ≫ u`, and `π_k ≫ ∑_{a ∈ Gal(k/L)} σ_a = |Gal(k/L)| • π_⊥` for
lifts `σ_a ∈ Gal(Ω/L)` of the elements of `Gal(k/L)`.

The Möbius components `e_k = ∑_{m ≤ k} μ(m, k) π_m` (`IncidenceAlgebra.moebiusComponent`) then
form a Möbius decomposition of `g_{∞*} g_∞^* K` for a complex `K`
(`AlgebraicGeometry.ProEtale.exists_galoisTowerMoebiusDecomposition`).
-/

@[expose] public section

universe u

open CategoryTheory Category Limits Preadditive

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

open FiniteGaloisIntermediateField ProEtale

variable {L Ω : Type u} [Field L] [Field Ω] [Algebra L Ω] {G : Scheme.{u}}
  (h : G ⟶ Spec (.of L))

/-- The transition maps intertwine the actions of the restrictions of `σ ∈ Gal(Ω/L)`. -/
lemma galoisLevelMap_comp_galoisLevelAction_restrictNormal [IsGalois L Ω]
    {L' L'' : FiniteGaloisIntermediateField L Ω} (hle : L' ≤ L'') (σ : Ω ≃ₐ[L] Ω) :
    galoisLevelMap Ω h hle ≫ galoisLevelAction h L' (σ.restrictNormal L') =
      galoisLevelAction h L'' (σ.restrictNormal L'') ≫ galoisLevelMap Ω h hle := by
  apply pullback.hom_ext
  · simp [galoisLevelMap]
  · simp only [galoisLevelMap, pullback.map, Category.assoc, pullbackAction_snd,
      pullback.lift_snd, pullback.lift_snd_assoc, pullbackAction_snd_assoc, specGaloisAction]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 2
    ext x
    exact (AlgEquiv.restrictNormal_commutes σ L' x).trans
      (AlgEquiv.restrictNormal_commutes σ L'' (IntermediateField.inclusion hle x)).symm

/-- The identity acts trivially on the finite levels. -/
lemma galoisLevelAction_one (L' : FiniteGaloisIntermediateField L Ω) :
    galoisLevelAction h L' 1 = 𝟙 _ := by
  apply pullback.hom_ext
  · simp
  · have e : CommRingCat.ofHom ((1 : L' ≃ₐ[L] L') : L' →+* L') = 𝟙 _ := rfl
    rw [pullbackAction_snd, specGaloisAction, e, Spec.map_id, Category.comp_id, Category.id_comp]

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing GaloisTower FiniteGaloisIntermediateField IncidenceAlgebra

variable {L Ω : Type u} [Field L] [Field Ω] [Algebra L Ω] [IsGalois L Ω] {G : Scheme.{u}}
  (h : G ⟶ Spec (.of L)) (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  [IsCommMonObj Λ]
  (hd : ∀ (j : (galoisTower Ω h).J)
    (N : CategoryTheory.Mod (Sheaf (ProEt.topology G) Ab.{u + 1}) (condensedRingObj Λ G)),
      IsIso (Fintype.card ((galoisTower Ω h).Γ j) • 𝟙 N))
  (M : CategoryTheory.Mod (Sheaf (ProEt.topology G) Ab.{u + 1}) (condensedRingObj Λ G))

/-- The averages over the images `N j k` of `Gal(Ω/k)` in `Gal(j/L)` are compatible with the
transition maps. -/
lemma galoisTower_transport_comp_levelAvg (k : FiniteGaloisIntermediateField L Ω)
    ⦃j j' : (galoisTower Ω h).J⦄ (hle : j ≤ j') :
    (galoisTower Ω h).transport Λ M hle ≫
        (galoisTower Ω h).levelAvg Λ M hd j' (restrictFixingSubgroup j' k) =
      (galoisTower Ω h).levelAvg Λ M hd j (restrictFixingSubgroup j k) ≫
        (galoisTower Ω h).transport Λ M hle := by
  refine (galoisTower Ω h).transport_comp_levelAvg Λ M hd hle _ _ ?_ ?_
  · rintro a ⟨σ, hσ, rfl⟩
    exact ⟨_, Subgroup.mem_map_of_mem _ hσ,
      galoisLevelMap_comp_galoisLevelAction_restrictNormal h hle σ⟩
  · rintro b ⟨σ, hσ, rfl⟩
    exact ⟨_, Subgroup.mem_map_of_mem _ hσ,
      galoisLevelMap_comp_galoisLevelAction_restrictNormal h hle σ⟩

set_option hygiene false in
/-- The projector `π_k : M_∞ ⟶ M_∞` onto the `Gal(Ω/k)`-invariants. -/
local notation3 "𝒫[" M ", " hc ", " k "]" => GaloisTower.proj (galoisTower Ω h) Λ M hd hc
  (fun x_proj ↦ restrictFixingSubgroup x_proj k) (galoisTower_transport_comp_levelAvg h Λ hd M k)

section Projectors

variable {M} (hc : IsColimit ((galoisTower Ω h).moduleCocone Λ M))

/-- **Product of the projectors**: `π_k ≫ π_m = π_(k ⊓ m)`. -/
lemma galoisTower_proj_comp_proj (k m : FiniteGaloisIntermediateField L Ω) :
    𝒫[M, hc, k] ≫ 𝒫[M, hc, m] = 𝒫[M, hc, k ⊓ m] :=
  (galoisTower Ω h).proj_comp_proj hc (galoisLevelAction_one h) _ _ _ _ _ _
    (fun j ↦ restrictFixingSubgroup_normal j m) (fun j ↦ restrictFixingSubgroup_sup j k m)

/-- The projector `π_j` is the identity on the image of the level `j`. -/
lemma galoisTower_infTransport_comp_proj_self (j : (galoisTower Ω h).J) :
    (galoisTower Ω h).infTransport Λ M j ≫ 𝒫[M, hc, j] = (galoisTower Ω h).infTransport Λ M j :=
  (galoisTower Ω h).infTransport_comp_proj_of_eq_bot hc (galoisLevelAction_one h) _ _ j
    (restrictFixingSubgroup_self j)

/-- The projector `π_⊥` is the invariant projector `τ ≫ u`. -/
lemma galoisTower_proj_bot :
    𝒫[M, hc, ⊥] = (galoisTower Ω h).trace Λ M hd hc ≫
      (infUnit Λ (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).app M :=
  (galoisTower Ω h).proj_eq_trace_comp_infUnit hc _ _ restrictFixingSubgroup_bot

/-- **The projectors and the Galois action**: for lifts `c a ∈ Gal(Ω/L)` of the elements
`a ∈ Gal(k/L)`, `π_k ≫ ∑_a σ_(c a) = |Gal(k/L)| • π_⊥`. -/
lemma galoisTower_proj_comp_sum_infAction (k : FiniteGaloisIntermediateField L Ω)
    (c : (k ≃ₐ[L] k) → (Ω ≃ₐ[L] Ω))
    (hcl : ∀ a, AlgEquiv.restrictNormalHom (F := L) (K₁ := Ω) k (c a) = a) :
    𝒫[M, hc, k] ≫ ∑ a, infAction Λ M
        (pullbackAction h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))
          specGaloisAction_comp (c a))
        (pullbackAction_fst h _ specGaloisAction_comp (c a)) =
      Fintype.card (k ≃ₐ[L] k) • 𝒫[M, hc, ⊥] := by
  have key : ∀ j : FiniteGaloisIntermediateField L Ω, k ≤ j →
      (galoisTower Ω h).infTransport Λ M j ≫ 𝒫[M, hc, k] ≫ ∑ a, infAction Λ M
        (pullbackAction h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))
          specGaloisAction_comp (c a))
        (pullbackAction_fst h _ specGaloisAction_comp (c a)) =
      (galoisTower Ω h).infTransport Λ M j ≫ (Fintype.card (k ≃ₐ[L] k) • 𝒫[M, hc, ⊥]) := by
    intro j hkj
    rw [(galoisTower Ω h).infTransport_comp_proj_comp_sum hc (fun x ↦ restrictFixingSubgroup x k)
      (galoisTower_transport_comp_levelAvg h Λ hd M k) j _ _
      (fun a ↦ AlgEquiv.restrictNormalHom (F := L) (K₁ := Ω) j (c a))
      (fun a ↦ pullbackAction_comp_galoisLevelProjection h j (c a))
      (bijective_restrictNormalHom_mul hkj c hcl),
      (galoisTower Ω h).levelAvg_top_comp_infTransport hc,
      galoisTower_proj_bot, comp_nsmul]
  refine hc.hom_ext fun j ↦ ?_
  change (galoisTower Ω h).infTransport Λ M j ≫ _ = (galoisTower Ω h).infTransport Λ M j ≫ _
  obtain ⟨j', hj, hkj'⟩ := exists_ge_ge (j : FiniteGaloisIntermediateField L Ω) k
  rw [← (galoisTower Ω h).transport_comp_infTransport Λ M hj, assoc, assoc, key j' hkj']

/-- **Naturality of the projectors** in the module object. -/
lemma galoisTower_proj_naturality {M M' : CategoryTheory.Mod (Sheaf (ProEt.topology G) Ab.{u + 1})
    (condensedRingObj Λ G)} (φ : M ⟶ M') (hc : IsColimit ((galoisTower Ω h).moduleCocone Λ M))
    (hc' : IsColimit ((galoisTower Ω h).moduleCocone Λ M'))
    (k : FiniteGaloisIntermediateField L Ω) :
    (infFunctor Λ (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).map φ ≫
        𝒫[M', hc', k] =
      𝒫[M, hc, k] ≫
        (infFunctor Λ (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).map φ :=
  (galoisTower Ω h).proj_naturality φ hc hc' _ _ _

end Projectors

variable (K : CochainComplex
    (CategoryTheory.Mod (Sheaf (ProEt.topology G) Ab.{u + 1}) (condensedRingObj Λ G)) ℤ)
  (hc : ∀ n, IsColimit ((galoisTower Ω h).moduleCocone Λ (K.X n)))

/-- **Existence of a Möbius decomposition** for the Galois tower of a Galois extension: the
Möbius components `e_k = ∑_{m ≤ k} μ(m, k) π_m` of the invariant projectors `π_m`, indexed by
the finite Galois subextensions `k`, whose averaging automorphisms are Galois automorphisms
`Spec σ`. -/
theorem exists_galoisTowerMoebiusDecomposition :
    ∃ D : (galoisTower Ω h).MoebiusDecomposition Λ hd K hc, ∀ i a, ∃ σ : Ω ≃ₐ[L] Ω,
      D.σ i a = pullbackAction h _ specGaloisAction_comp σ := by
  classical
  choose c hcl using fun (k : FiniteGaloisIntermediateField L Ω) (a : k ≃ₐ[L] k) ↦
    AlgEquiv.restrictNormalHom_surjective (F := L) (K₁ := k) Ω a
  obtain ⟨π, hπdef⟩ : ∃ π : ∀ n, FiniteGaloisIntermediateField L Ω →
      End ((infFunctor Λ (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).obj
        (K.X n)), ∀ n k, (π n k).asHom = 𝒫[K.X n, hc n, k] :=
    ⟨fun n k ↦ End.of 𝒫[K.X n, hc n, k], fun _ _ ↦ rfl⟩
  have hπ : ∀ n x y, π n x * π n y = π n (x ⊓ y) := fun n x y ↦ by
    apply End.ext
    rw [End.mul_asHom, inf_comm, hπdef, hπdef, hπdef]
    exact galoisTower_proj_comp_proj h Λ hd (hc n) y x
  obtain ⟨e, he⟩ : ∃ e : ∀ n, FiniteGaloisIntermediateField L Ω →
      End ((infFunctor Λ (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).obj
        (K.X n)), ∀ n k, e n k = moebiusComponent (π n) k := ⟨_, fun _ _ ↦ rfl⟩
  refine ⟨{ ι := FiniteGaloisIntermediateField L Ω
            i₀ := ⊥
            F := fun j ↦ Finset.Iic j
            e := fun k n ↦ (e n k).asHom
            comm := fun k n m ↦ ?_
            e_i₀ := fun n ↦ ?_
            A := fun k ↦ Fin (Fintype.card (k ≃ₐ[L] k))
            σ := fun k i ↦ pullbackAction h _ specGaloisAction_comp
              (c k ((Fintype.equivFin _).symm i))
            hσ := fun k i ↦ pullbackAction_fst h _ specGaloisAction_comp _
            hσj := fun k i j ↦ ⟨_, pullbackAction_comp_galoisLevelProjection h j _⟩
            card := fun k N ↦ by
              rw [Fintype.card_fin]
              exact hd k N
            sum_comp_infAction := fun k hk n ↦ ?_
            infTransport_comp_eq_zero := fun j n k hk ↦ ?_
            infTransport_comp_sum := fun j n ↦ ?_ }, fun _ _ ↦ ⟨_, rfl⟩⟩
  · have h₁ : (e n k).asHom ≫ (infFunctor Λ _).map (K.d n m) =
        ∑ x ∈ Finset.Iic k, mu ℤ x k • ((π n x).asHom ≫
          (infFunctor Λ _).map (K.d n m)) := by
      rw [he]
      exact map_moebiusComponent ((Preadditive.rightComp ((infFunctor Λ _).obj (K.X n))
        ((infFunctor Λ _).map (K.d n m))).comp End.addEquiv.toAddMonoidHom) (π n) k
    have h₂ : (infFunctor Λ _).map (K.d n m) ≫ (e m k).asHom =
        ∑ x ∈ Finset.Iic k, mu ℤ x k • ((infFunctor Λ _).map (K.d n m) ≫
          (π m x).asHom) := by
      rw [he]
      exact map_moebiusComponent ((Preadditive.leftComp ((infFunctor Λ _).obj (K.X m))
        ((infFunctor Λ _).map (K.d n m))).comp End.addEquiv.toAddMonoidHom) (π m) k
    rw [h₁, h₂]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [hπdef, hπdef, galoisTower_proj_naturality]
  · change (e n ⊥).asHom = _
    rw [he, moebiusComponent_bot, hπdef]
    exact galoisTower_proj_bot h Λ hd (hc n)
  · have h₁ : (e n k).asHom ≫ (π n k).asHom = (e n k).asHom := by
      rw [he]
      simpa only [End.mul_asHom] using congrArg End.asHom
        ((mul_moebiusComponent (hπ n) k k).trans (ite_eq_left le_rfl))
    have h₂ : (e n k).asHom ≫ (π n ⊥).asHom = 0 := by
      rw [he]
      simpa only [End.mul_asHom, End.zero_asHom] using congrArg End.asHom
        ((mul_moebiusComponent (hπ n) k ⊥).trans
          (ite_eq_right fun hle ↦ hk (le_bot_iff.1 hle)))
    change ∑ i, (e n k).asHom ≫ _ = 0
    rw [← comp_sum, ← h₁, assoc, hπdef,
      Fintype.sum_equiv (Fintype.equivFin _).symm _ (fun a ↦ infAction Λ (K.X n)
        (pullbackAction h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))
          specGaloisAction_comp (c k a))
        (pullbackAction_fst h _ specGaloisAction_comp (c k a))) fun _ ↦ rfl,
      galoisTower_proj_comp_sum_infAction h Λ hd (hc n) k (c k) (hcl k), comp_nsmul, ← hπdef,
      h₂, nsmul_zero]
  · have h₀ : (π n j).asHom ≫ (e n k).asHom = 0 := by
      rw [he]
      simpa only [End.mul_asHom, End.zero_asHom] using congrArg End.asHom
        ((moebiusComponent_mul (hπ n) k j).trans
          (ite_eq_right fun hle ↦ hk (Finset.mem_Iic.2 hle)))
    change _ ≫ (e n k).asHom = 0
    rw [← galoisTower_infTransport_comp_proj_self h Λ hd (hc n) j, ← hπdef, assoc, h₀,
      comp_zero]
  · have hs : ∑ k ∈ Finset.Iic (α := FiniteGaloisIntermediateField L Ω) j, e n k = π n j := by
      simp only [he]
      exact sum_Iic_moebiusComponent (π n) j
    have hs' := congrArg End.asHom hs
    simp only [End.sum_asHom] at hs'
    refine (congrArg ((galoisTower Ω h).infTransport Λ (K.X n) j ≫ ·) hs').trans ?_
    rw [hπdef, galoisTower_infTransport_comp_proj_self]

end AlgebraicGeometry.ProEtale
