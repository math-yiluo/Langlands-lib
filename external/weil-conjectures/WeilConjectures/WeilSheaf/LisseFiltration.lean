/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Free
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseAbelian
public import WeilConjectures.WeilSheaf.StalkFunctor
public import WeilConjectures.WeilSheaf.Triangle

/-!
# Jordan–Hölder filtrations of lisse Weil sheaves

On a `k₀`-scheme `X` of finite type, every lisse Weil sheaf `G` admits a finite filtration
`0 = H₀ ↪ H₁ ↪ ⋯ ↪ Hₙ ≅ G` by lisse Weil subsheaves whose successive quotients are irreducible
lisse (`AlgebraicGeometry.WeilSheaf.IsLisse.exists_filtration_isIrreducibleLisse`).

## Proof

Kernels and cokernels of morphisms of lisse Weil sheaves are lisse
(`AlgebraicGeometry.WeilSheaf.IsLisse.kernel_cokernel`), by the corresponding statement for
`ℓ`-adic sheaves on the locally Noetherian scheme `X̄`
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.kernel_cokernel`).

The geometric fiber `X̄` is a Noetherian space; choose geometric points `s₁, …, s_N` over a
closed point of each irreducible component of `X̄`. The *stalk rank* `∑ᵢ dim G_{sᵢ}`
(`AlgebraicGeometry.WeilSheaf.stalkRank`) is additive in short exact sequences, the stalk
functors being exact, and it vanishes on a lisse sheaf only if the sheaf is zero
(`AlgebraicGeometry.WeilSheaf.isZero_of_stalkRank_eq_zero`): the rank of a lisse sheaf is
constant on the irreducible components.

By strong induction on the stalk rank, a nonzero lisse `G` has a proper lisse subsheaf `K` of
maximal stalk rank; `K` has a filtration by induction, and `G / K` is irreducible lisse: for a
nonzero proper lisse subsheaf `T ⊆ G / K`, the kernel of `G ⟶ (G / K) / T` would be a proper
lisse subsheaf of `G` of stalk rank `rk K + rk T > rk K`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.IsLisse.kernel_cokernel`: lisse Weil sheaves are closed under
  kernels and cokernels.
- `AlgebraicGeometry.WeilSheaf.IsLisse.exists_filtration_isIrreducibleLisse`: the filtration.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology ZeroObject

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

section Lisse

variable (k₀ l X) in
/-- The underlying `ℓ`-adic sheaf on `X̄` of a Weil sheaf, as a functor. -/
noncomputable abbrev carrierFunctor :
    WeilSheaf k₀ l X ⥤ AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  (WeilSheaf.objectProperty k₀ l X).ι ⋙ Endofunctor.IsoAlgebra.forget _

instance : PreservesFiniteLimits (carrierFunctor k₀ l X) := by
  unfold carrierFunctor
  infer_instance

instance : PreservesFiniteColimits (carrierFunctor k₀ l X) := by
  unfold carrierFunctor
  infer_instance

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- Lissity is invariant under isomorphism. -/
theorem IsLisse.of_iso {F G : WeilSheaf k₀ l X} (e : F ≅ G) (hF : F.IsLisse) : G.IsLisse :=
  IsAdicLisseSheaf.of_iso ((carrierFunctor k₀ l X).mapIso e) hF

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- A zero Weil sheaf is lisse. -/
theorem isLisse_of_isZero {F : WeilSheaf k₀ l X} (hF : IsZero F) : F.IsLisse :=
  IsAdicLisseSheaf.of_isZero (isZero_iff_isZero_carrier.1 hF)

/-- **Kernels and cokernels of lisse Weil sheaves are lisse.** -/
theorem IsLisse.kernel_cokernel {F G : WeilSheaf k₀ l X} (hF : F.IsLisse) (hG : G.IsLisse)
    (φ : F ⟶ G) : (kernel φ).IsLisse ∧ (cokernel φ).IsLisse := by
  obtain ⟨h₁, h₂⟩ := IsAdicLisseSheaf.kernel_cokernel hF hG ((carrierFunctor k₀ l X).map φ)
  exact ⟨h₁.of_iso (PreservesKernel.iso (carrierFunctor k₀ l X) φ).symm,
    h₂.of_iso (PreservesCokernel.iso (carrierFunctor k₀ l X) φ).symm⟩

/-- **Extensions of lisse Weil sheaves are lisse.** -/
theorem IsLisse.of_mono_cokernel {F G : WeilSheaf k₀ l X} (φ : F ⟶ G) [Mono φ]
    (hF : F.IsLisse) (hQ : (cokernel φ).IsLisse) : G.IsLisse := by
  have hS : (ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel φ))
      inferInstance inferInstance
  exact IsAdicLisseSheaf.of_shortExact (hS.map_of_exact (carrierFunctor k₀ l X)) hF hQ

variable (k₀ l X) in
/-- The property of a Weil sheaf of being irreducible lisse. -/
abbrev isIrreducibleLisse : ObjectProperty (WeilSheaf k₀ l X) :=
  fun F ↦ F.IsIrreducibleLisse

/-- Being irreducible lisse is invariant under isomorphism. -/
instance : ObjectProperty.IsClosedUnderIsomorphisms
    (isIrreducibleLisse k₀ l X) where
  of_iso {F G} e hF := by
    refine ⟨hF.1.of_iso e, fun h ↦ hF.2.1 (h.of_iso e), fun T i hi hT ↦ ?_⟩
    obtain h | h := hF.2.2 T (i ≫ e.inv) inferInstance hT
    · exact Or.inl h
    · exact Or.inr (IsIso.of_isIso_comp_right i e.inv)

end Lisse

section Rank

variable {N : ℕ}
  (s : Fin N → (Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))

/-- The *stalk rank* of a Weil sheaf at finitely many geometric points: the sum of the
dimensions of its stalks there. -/
noncomputable def stalkRank (G : WeilSheaf k₀ l X) : ℕ :=
  ∑ i, Module.finrank (PadicAlgCl l)
    ((WeilCoefficients.toModuleCat l).obj ((stalkFunctor k₀ l (s i)).obj G))

/-- The stalk rank is additive in short exact sequences. -/
theorem stalkRank_add {F G : WeilSheaf k₀ l X} (φ : F ⟶ G) [Mono φ] :
    stalkRank s G = stalkRank s F + stalkRank s (cokernel φ) := by
  rw [stalkRank, stalkRank, stalkRank, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hS : (ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel φ))
      inferInstance inferInstance
  have : PreservesFiniteLimits (stalkFunctor k₀ l (s i)) := by
    unfold stalkFunctor sheafFunctor
    infer_instance
  have : (stalkFunctor k₀ l (s i)).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  have hS' := hS.map (stalkFunctor k₀ l (s i))
  let Φ := stalkFunctor k₀ l (s i) ⋙ WeilCoefficients.toModuleCat l
  have hT : (ShortComplex.mk (Φ.map φ) (Φ.map (cokernel.π φ))
      (by rw [← Φ.map_comp, cokernel.condition, Φ.map_zero])).ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.moduleCat_exact_iff]
      intro x hx
      obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 hS'.exact x hx
      exact ⟨y, hy⟩
    · rw [ModuleCat.mono_iff_injective]
      have h1 := hS'.mono_f
      rw [ModuleCat.mono_iff_injective] at h1
      exact h1
    · rw [ModuleCat.epi_iff_surjective]
      have h1 := hS'.epi_g
      rw [ModuleCat.epi_iff_surjective] at h1
      exact h1
  have : FiniteDimensional (PadicAlgCl l) (Φ.obj F) := F.finiteDimensional_stalkObj (s i)
  have : FiniteDimensional (PadicAlgCl l) (Φ.obj (cokernel φ)) :=
    (cokernel φ).finiteDimensional_stalkObj (s i)
  exact ModuleCat.free_shortExact_finrank_add hT rfl rfl

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The stalk rank is invariant under isomorphism. -/
theorem stalkRank_congr {F G : WeilSheaf k₀ l X} (e : F ≅ G) : stalkRank s F = stalkRank s G :=
  Finset.sum_congr rfl fun i _ ↦
    (((stalkFunctor k₀ l (s i) ⋙ WeilCoefficients.toModuleCat l).mapIso e).toLinearEquiv).finrank_eq

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- **A lisse Weil sheaf of stalk rank zero is zero**, if every point of `X̄` is a
specialization of a point which also specializes to the image of one of the `sᵢ`: the rank of
a lisse sheaf is constant along specializations. -/
theorem isZero_of_stalkRank_eq_zero
    (hs : ∀ y, ∃ (η : _) (i : Fin N), η ⤳ y ∧
      η ⤳ (s i).base (IsLocalRing.closedPoint (AlgebraicClosure k₀)))
    {G : WeilSheaf k₀ l X} (hG : G.IsLisse) (h : stalkRank s G = 0) : IsZero G := by
  refine isZero_iff_isZero_carrier.2
    (hG.isZero_of_subsingleton_globalSections_upperStar (AlgebraicClosure k₀) fun y ↦ ?_)
  obtain ⟨η, i, h₁, h₂⟩ := hs y
  refine ⟨η, s i, h₁, h₂, ?_⟩
  have : FiniteDimensional (PadicAlgCl l)
      ((WeilCoefficients.toModuleCat l).obj ((stalkFunctor k₀ l (s i)).obj G)) :=
    G.finiteDimensional_stalkObj (s i)
  have h0 := (Finset.sum_eq_zero_iff.1 h) i (Finset.mem_univ i)
  have h0 := Module.finrank_zero_iff.1 h0
  exact h0

omit [Finite k₀] in
variable (k₀ l X) in
/-- On a `k₀`-scheme of finite type there are finitely many geometric points `sᵢ` of `X̄` such
that every point of `X̄` is a specialization of a point which also specializes to the image of
some `sᵢ`: geometric points over a closed point of each of the finitely many irreducible
components of `X̄`. -/
theorem exists_geometricPoints_specializes [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] :
    ∃ (N : ℕ) (s : Fin N →
      (Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)),
      ∀ y, ∃ (η : _) (i : Fin N), η ⤳ y ∧
        η ⤳ (s i).base (IsLocalRing.closedPoint (AlgebraicClosure k₀)) := by
  set f := X ↘ Spec (CommRingCat.of k₀)
  have : IsNoetherian f.geometricFiber := {}
  have hC (C : irreducibleComponents f.geometricFiber) :
      ∃ t : Spec (.of (AlgebraicClosure k₀)) ⟶ f.geometricFiber,
        t.base (IsLocalRing.closedPoint (AlgebraicClosure k₀)) ∈ (C : Set f.geometricFiber) := by
    obtain ⟨x, hxC, hx⟩ := (isClosed_of_mem_irreducibleComponents _ C.2).exists_closed_singleton
      (C.2.1 : IsIrreducible (C : Set f.geometricFiber)).nonempty
    obtain ⟨t, ht⟩ := f.geometricFiberToAlgebraicClosure.exists_spec_base_eq_of_isClosed x hx
    exact ⟨t, ht ▸ hxC⟩
  choose t ht using hC
  have : Finite (irreducibleComponents f.geometricFiber) :=
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents).to_subtype
  let e := Finite.equivFin (irreducibleComponents f.geometricFiber)
  refine ⟨Nat.card _, fun i ↦ t (e.symm i), fun y ↦ ?_⟩
  let C : irreducibleComponents f.geometricFiber :=
    ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩
  obtain ⟨η, hη⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := y))
    isClosed_irreducibleComponent
  refine ⟨η, e C, hη.specializes mem_irreducibleComponent, ?_⟩
  have hC : e.symm (e C) = C := e.symm_apply_apply C
  simpa only [hC] using hη.specializes (ht C)

end Rank

/-- Every lisse Weil sheaf on a `k₀`-scheme of finite type admits a finite filtration whose
successive quotients are irreducible lisse, as a filtration closure. -/
theorem IsLisse.filtrationClosure_isIrreducibleLisse
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] {G : WeilSheaf k₀ l X} (hG : G.IsLisse) :
    (WeilSheaf.isIrreducibleLisse k₀ l X).filtrationClosure G := by
  obtain ⟨N, s, hs⟩ := exists_geometricPoints_specializes k₀ X
  suffices H : ∀ r, ∀ G : WeilSheaf k₀ l X, G.IsLisse → stalkRank s G = r →
      (WeilSheaf.isIrreducibleLisse k₀ l X).filtrationClosure G from
    H _ G hG rfl
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro G hG hr
  by_cases hG0 : IsZero G
  · exact .of_isZero hG0
  -- a proper lisse subsheaf of maximal stalk rank
  let S : Set ℕ := {m | ∃ (K : WeilSheaf k₀ l X) (i : K ⟶ G), Mono i ∧ K.IsLisse ∧ ¬ IsIso i ∧
    stalkRank s K = m}
  have hSne : S.Nonempty := by
    refine ⟨_, 0, (0 : 0 ⟶ G), inferInstance, isLisse_of_isZero (isZero_zero _), fun h ↦ ?_,
      rfl⟩
    exact hG0 ((isZero_zero _).of_iso (asIso (0 : 0 ⟶ G)).symm)
  have hSb : BddAbove S := by
    refine ⟨stalkRank s G, ?_⟩
    rintro _ ⟨K, i, hi, -, -, rfl⟩
    have := stalkRank_add s i
    omega
  obtain ⟨K, i, hi, hK, hiso, hKr⟩ := Nat.sSup_mem hSne hSb
  have hmax (K' : WeilSheaf k₀ l X) (i' : K' ⟶ G) (hi' : Mono i') (hK' : K'.IsLisse)
      (hiso' : ¬ IsIso i') : stalkRank s K' ≤ stalkRank s K :=
    hKr ▸ le_csSup hSb ⟨K', i', hi', hK', hiso', rfl⟩
  have hQ : (cokernel i).IsLisse := (hK.kernel_cokernel hG i).2
  have hQ0 : ¬ IsZero (cokernel i) := fun h ↦ by
    have : Epi i := Preadditive.epi_of_isZero_cokernel i h
    exact hiso (isIso_of_mono_of_epi i)
  have hrQ : stalkRank s (cokernel i) ≠ 0 := fun h ↦ hQ0 (isZero_of_stalkRank_eq_zero s hs hQ h)
  have hadd := stalkRank_add s i
  refine .of_mono i (ih _ (by omega) K hK rfl) ⟨hQ, hQ0, fun T j hj hT ↦ ?_⟩
  by_contra! hcon
  obtain ⟨hT0, hj'⟩ := hcon
  have hR : (cokernel j).IsLisse := (hT.kernel_cokernel hQ j).2
  let g := cokernel.π i ≫ cokernel.π j
  have hK' : (kernel g).IsLisse := (hG.kernel_cokernel hR g).1
  have hm : ¬ IsIso (kernel.ι g) := by
    intro hm
    have hg0 : g = 0 := by rw [← cancel_epi (kernel.ι g), kernel.condition, comp_zero]
    have hj0 : cokernel.π j = 0 := by
      rw [← cancel_epi (cokernel.π i), comp_zero]
      exact hg0
    have : Epi j := Abelian.epi_of_cokernel_π_eq_zero j hj0
    exact hj' (isIso_of_mono_of_epi j)
  have h₁ := hmax _ (kernel.ι g) inferInstance hK' hm
  let i' : K ⟶ kernel g := kernel.lift g i (by simp [g])
  have : Mono i' := mono_of_mono_fac (kernel.lift_ι g i _)
  have h₂ := stalkRank_add s i'
  have h₃ := stalkRank_add s (kernel.ι g)
  have h₄ := stalkRank_congr s (ObjectProperty.cokernelKernelιIsoOfEpi g)
  have h₅ := stalkRank_add s j
  exact hT0 (isZero_of_stalkRank_eq_zero s hs hT (by omega))

/-- **Jordan–Hölder filtrations of lisse Weil sheaves.** Every lisse Weil sheaf `G` on a
`k₀`-scheme of finite type admits a finite filtration `0 = H₀ ↪ H₁ ↪ ⋯ ↪ Hₙ ≅ G` by lisse Weil
subsheaves whose successive quotients are irreducible lisse. -/
theorem IsLisse.exists_filtration_isIrreducibleLisse
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] {G : WeilSheaf k₀ l X} (hG : G.IsLisse) :
    ∃ (n : ℕ) (H : Fin (n + 1) → WeilSheaf k₀ l X) (φ : ∀ i : Fin n, H i.castSucc ⟶ H i.succ),
      IsZero (H 0) ∧ IsIsomorphic (H (Fin.last n)) G ∧ (∀ i, Mono (φ i)) ∧
        (∀ i, (H i).IsLisse) ∧ ∀ i : Fin n, (cokernel (φ i)).IsIrreducibleLisse := by
  obtain ⟨n, H, φ, h0, hlast, hmono, hirr⟩ :=
    ObjectProperty.filtrationClosure_iff.1 hG.filtrationClosure_isIrreducibleLisse
  refine ⟨n, H, φ, h0, hlast, hmono, ?_, hirr⟩
  rintro ⟨i, hi⟩
  induction i with
  | zero => exact isLisse_of_isZero h0
  | succ i ih =>
    have hi' : i < n := by omega
    have := hmono ⟨i, hi'⟩
    exact IsLisse.of_mono_cokernel (φ ⟨i, hi'⟩) (ih _) (hirr _).1

end AlgebraicGeometry.WeilSheaf
