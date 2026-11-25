/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Free
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedFieldExact
public import WeilConjectures.SixFunctors.ProEtale.Adic.GeometricFrobenius
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseAbelian
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromy

/-!
# Irreducible lisse subsheaves of a lisse `ℓ`-adic sheaf

Let `Y` be a locally Noetherian scheme with a monodromy of lisse sheaves `M` which is an
equivalence at a geometric point `t`
(`AlgebraicGeometry.ProEtale.LisseMonodromy.IsEquivalenceAt`), e.g. `Y` connected, regular and
locally Noetherian (`AlgebraicGeometry.ProEtale.exists_lisseMonodromy`). We only use that the
stalk functor at `t` is faithful on lisse sheaves; the *rank*
`AlgebraicGeometry.ProEtale.adicStalkRank` of a lisse sheaf is the dimension of its stalk at `t`.

* The rank is additive in short exact sequences of lisse sheaves, and a lisse sheaf of rank zero
  is zero.
* Among infinitely many irreducible lisse subsheaves `T₀, T₁, …` of a lisse sheaf `V`, two are
  isomorphic (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.exists_iso_of_mono`): as long as
  `T_k` is not isomorphic to an earlier `T_j`, it meets the sum `P_k` of the earlier ones
  trivially, so that the rank of `P_k` grows with `k`.
* For an irreducible lisse `S`, a lisse `V` and an autoequivalence `Φ` of `ℓ`-adic sheaves
  commuting with scalars, together with `Φ S ≅ S` and `Φ V ≅ V`, there is a monomorphism
  `S ⟶ V` which is an eigenvector of the induced `ℚ̄_ℓ`-linear operator on the
  finite-dimensional space `Hom(S, V)`
  (`AlgebraicGeometry.ProEtale.IsIrreducibleAdicLocalSystem.exists_mono_map_comp_eq`), since
  `ℚ̄_ℓ` is algebraically closed.
-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

section Iso

variable {X Y : Scheme.{u}}

/-- The pushforward of a lisse sheaf along an isomorphism of schemes is lisse: it is the pullback
along the inverse isomorphism. -/
theorem IsAdicLisseSheaf.adicLowerStar_of_iso (e : X ≅ Y) {F : AdicSheaf l X}
    (hF : IsAdicLisseSheaf F) : IsAdicLisseSheaf ((e.hom)_*ᵃ[l].obj F) :=
  (hF.upperStar e.inv).of_iso ((adicUpperStarIsoLowerStarInv l e.symm).app F)

/-- The pushforward of an irreducible local system along an isomorphism of schemes is an
irreducible local system: the pushforward along `e.inv` is an inverse equivalence, and both
pushforwards preserve lisse sheaves. -/
theorem IsIrreducibleAdicLocalSystem.adicLowerStar_of_iso (e : X ≅ Y) {F : AdicSheaf l X}
    (hF : IsIrreducibleAdicLocalSystem F) :
    IsIrreducibleAdicLocalSystem ((e.hom)_*ᵃ[l].obj F) := by
  obtain ⟨hl, hz, h⟩ := hF
  let E := adicLowerStarEquivalence l e
  refine ⟨hl.adicLowerStar_of_iso e,
    fun h0 ↦ hz ((E.inverse.map_isZero h0).of_iso (E.unitIso.app F)), fun G i _ hG ↦ ?_⟩
  rcases h (E.inverse.obj G) (E.inverse.map i ≫ E.unitIso.inv.app F) inferInstance
    (hG.adicLowerStar_of_iso e.symm) with h' | h'
  · exact Or.inl ((E.functor.map_isZero h').of_iso (E.counitIso.app G).symm)
  · have : IsIso (E.inverse.map i) := IsIso.of_isIso_comp_right _ (E.unitIso.inv.app F)
    exact Or.inr (isIso_of_reflects_iso i E.inverse)

end Iso

section Schur

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y]

/-- A nonzero morphism from an irreducible local system to a lisse sheaf is a monomorphism: its
kernel is a lisse subsheaf which is not everything. -/
theorem IsIrreducibleAdicLocalSystem.mono_of_ne_zero {S G : AdicSheaf l Y}
    (hS : IsIrreducibleAdicLocalSystem S) (hG : IsAdicLisseSheaf G) (φ : S ⟶ G) (hφ : φ ≠ 0) :
    Mono φ := by
  rcases hS.2.2 (kernel φ) (kernel.ι φ) inferInstance (hS.1.kernel_cokernel hG φ).1 with
    h | h
  · exact Preadditive.mono_of_isZero_kernel φ h
  · exact absurd ((cancel_epi (kernel.ι φ)).1 (by rw [kernel.condition, comp_zero])) hφ

end Schur

section Rank

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)

/-- The *rank* of an `ℓ`-adic sheaf at a geometric point `t`: the dimension of its stalk. -/
noncomputable def adicStalkRank (F : AdicSheaf l Y) : ℕ :=
  Module.finrank (PadicAlgCl l)
    ((WeilCoefficients.toModuleCat l).obj ((stalkFunctor l t).obj F.X))

/-- The stalks of a lisse sheaf are finite-dimensional. -/
theorem IsAdicLisseSheaf.finiteDimensional_stalk {F : AdicSheaf l Y} (hF : IsAdicLisseSheaf F) :
    FiniteDimensional (PadicAlgCl l)
      ((WeilCoefficients.toModuleCat l).obj ((stalkFunctor l t).obj F.X)) :=
  (hF.upperStar t).isAdicConstructibleSheaf.finiteDimensional_globalSections

/-- The rank is invariant under isomorphism. -/
theorem adicStalkRank_congr {F G : AdicSheaf l Y} (e : F ≅ G) :
    adicStalkRank t F = adicStalkRank t G :=
  ((AdicSheaf.forget Y ⋙ stalkFunctor l t ⋙ WeilCoefficients.toModuleCat l).mapIso
    e).toLinearEquiv.finrank_eq

/-- **The rank is additive** in short exact sequences of lisse sheaves: the stalk functor is
exact. -/
theorem adicStalkRank_add [IsLocallyNoetherian Y] {F G : AdicSheaf l Y} (hF : IsAdicLisseSheaf F)
    (hG : IsAdicLisseSheaf G) (φ : F ⟶ G) [Mono φ] :
    adicStalkRank t G = adicStalkRank t F + adicStalkRank t (cokernel φ) := by
  have hS : (ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel φ))
      inferInstance inferInstance
  have : PreservesFiniteLimits (AdicSheaf.forget Y ⋙ stalkFunctor l t) := by
    unfold stalkFunctor
    infer_instance
  have : (AdicSheaf.forget (l := l) Y).PreservesEpimorphisms := inferInstance
  have : (stalkFunctor l t).PreservesEpimorphisms := by
    unfold stalkFunctor
    infer_instance
  have : (AdicSheaf.forget Y ⋙ stalkFunctor l t).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_comp _ _
  have : (AdicSheaf.forget Y ⋙ stalkFunctor l t).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  have : Epi ((AdicSheaf.forget Y ⋙ stalkFunctor l t).map (cokernel.π φ)) :=
    Functor.map_epi _ _
  have hS' := hS.map (AdicSheaf.forget Y ⋙ stalkFunctor l t)
  let Φ := AdicSheaf.forget Y ⋙ stalkFunctor l t ⋙ WeilCoefficients.toModuleCat l
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
  have : FiniteDimensional (PadicAlgCl l) (Φ.obj F) := hF.finiteDimensional_stalk t
  have : FiniteDimensional (PadicAlgCl l) (Φ.obj (cokernel φ)) :=
    (hF.kernel_cokernel hG φ).2.finiteDimensional_stalk t
  exact ModuleCat.free_shortExact_finrank_add hT rfl rfl

/-- The rank of a lisse subsheaf is at most the rank of the sheaf. -/
theorem adicStalkRank_le_of_mono [IsLocallyNoetherian Y] {F G : AdicSheaf l Y}
    (hF : IsAdicLisseSheaf F) (hG : IsAdicLisseSheaf G) (φ : F ⟶ G) [Mono φ] :
    adicStalkRank t F ≤ adicStalkRank t G := by
  rw [adicStalkRank_add t hF hG φ]
  exact Nat.le_add_right _ _

variable {M : LisseMonodromy l Y Ω}

/-- **A lisse sheaf of rank zero is zero**, if the stalk functor at `t` is faithful on lisse
sheaves. -/
theorem IsAdicLisseSheaf.isZero_of_adicStalkRank_eq_zero (hM : M.IsEquivalenceAt t)
    {F : AdicSheaf l Y} (hF : IsAdicLisseSheaf F) (h : adicStalkRank t F = 0) : IsZero F := by
  have := hF.finiteDimensional_stalk t
  have : Subsingleton ((WeilCoefficients.toModuleCat l).obj ((stalkFunctor l t).obj F.X)) :=
    Module.finrank_zero_iff.1 h
  have : Subsingleton ((lisseStalk l t).obj ⟨F, hF⟩) := this
  rw [IsZero.iff_id_eq_zero]
  have h' : 𝟙 (⟨F, hF⟩ : LisseSheaf l Y) = ObjectProperty.homMk 0 :=
    hM.faithful _ _ (ModuleCat.hom_ext (LinearMap.ext fun _ ↦ Subsingleton.elim _ _))
  exact congrArg (·.hom) h'

/-- A monomorphism of lisse sheaves of the same rank is an isomorphism. -/
theorem isIso_of_adicStalkRank_eq [IsLocallyNoetherian Y] (hM : M.IsEquivalenceAt t)
    {F G : AdicSheaf l Y} (hF : IsAdicLisseSheaf F) (hG : IsAdicLisseSheaf G) (φ : F ⟶ G)
    [Mono φ] (h : adicStalkRank t F = adicStalkRank t G) : IsIso φ := by
  have h0 := (hF.kernel_cokernel hG φ).2.isZero_of_adicStalkRank_eq_zero t hM
    (by have := adicStalkRank_add t hF hG φ; omega)
  have : Epi φ := Preadditive.epi_of_isZero_cokernel φ h0
  exact isIso_of_mono_of_epi φ

/-- An irreducible local system has positive rank. -/
theorem IsIrreducibleAdicLocalSystem.adicStalkRank_pos (hM : M.IsEquivalenceAt t)
    {S : AdicSheaf l Y} (hS : IsIrreducibleAdicLocalSystem S) : 0 < adicStalkRank t S :=
  Nat.pos_of_ne_zero fun h ↦ hS.2.1 (hS.1.isZero_of_adicStalkRank_eq_zero t hM h)

/-- The inductive step of `AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.exists_iso_of_mono`: if
every irreducible lisse subsheaf of a lisse subsheaf `P ⊆ V` is isomorphic to one of
`T₀, …, T_{k-1}`, then either the irreducible lisse subsheaf `T_k ⊆ V` is isomorphic to one of
them, or `P + T_k` is a lisse subsheaf of rank `rk P + rk T_k` all of whose irreducible lisse
subsheaves are isomorphic to one of `T₀, …, T_k`. -/
theorem IsAdicLisseSheaf.exists_iso_or_exists_mono_succ [IsLocallyNoetherian Y]
    {V : AdicSheaf l Y} (hV : IsAdicLisseSheaf V) (T : ℕ → AdicSheaf l Y)
    (hT : ∀ j, IsIrreducibleAdicLocalSystem (T j)) (ι : ∀ j, T j ⟶ V) [∀ j, Mono (ι j)] (k : ℕ)
    {P : AdicSheaf l Y} (p : P ⟶ V) [Mono p] (hP : IsAdicLisseSheaf P)
    (hPk : ∀ (S : AdicSheaf l Y) (q : S ⟶ P), Mono q → IsIrreducibleAdicLocalSystem S →
      ∃ j < k, Nonempty (S ≅ T j)) :
    (∃ j < k, Nonempty (T k ≅ T j)) ∨
      ∃ (P' : AdicSheaf l Y) (p' : P' ⟶ V), Mono p' ∧ IsAdicLisseSheaf P' ∧
        adicStalkRank t P' = adicStalkRank t P + adicStalkRank t (T k) ∧
        ∀ (S : AdicSheaf l Y) (q : S ⟶ P'), Mono q → IsIrreducibleAdicLocalSystem S →
          ∃ j < k + 1, Nonempty (S ≅ T j) := by
  have hQ : IsAdicLisseSheaf (cokernel p) := (hP.kernel_cokernel hV p).2
  let g := ι k ≫ cokernel.π p
  rcases (hT k).2.2 (kernel g) (kernel.ι g) inferInstance
    ((hT k).1.kernel_cokernel hQ g).1 with h0 | hiso
  swap
  · -- `T_k ⊆ P`
    have hg : ι k ≫ cokernel.π p = 0 := (cancel_epi (kernel.ι g)).1 (by
      rw [comp_zero]
      exact kernel.condition g)
    have : Mono (Abelian.monoLift p (ι k) hg) :=
      mono_of_mono_fac (Abelian.monoLift_comp p (ι k) hg)
    exact Or.inl (hPk _ (Abelian.monoLift p (ι k) hg) inferInstance (hT k))
  -- `T_k ∩ P = 0`
  have : Mono g := Preadditive.mono_of_isZero_kernel g h0
  have hQ' : IsAdicLisseSheaf (cokernel g) := ((hT k).1.kernel_cokernel hQ g).2
  let h := cokernel.π p ≫ cokernel.π g
  have hP' : IsAdicLisseSheaf (kernel h) := (hV.kernel_cokernel hQ' h).1
  refine Or.inr ⟨kernel h, kernel.ι h, inferInstance, hP', ?_, fun S q _ hS ↦ ?_⟩
  · have h₁ := adicStalkRank_add t hP hV p
    have h₂ := adicStalkRank_add t (hT k).1 hQ g
    have h₃ := adicStalkRank_add t hP' hV (kernel.ι h)
    have h₄ := adicStalkRank_congr t (ObjectProperty.cokernelKernelιIsoOfEpi h)
    omega
  by_cases h₁ : q ≫ kernel.ι h ≫ cokernel.π p = 0
  · have h₁' : (q ≫ kernel.ι h) ≫ cokernel.π p = 0 := by rw [Category.assoc, h₁]
    have : Mono (Abelian.monoLift p (q ≫ kernel.ι h) h₁') :=
      mono_of_mono_fac (Abelian.monoLift_comp p _ h₁')
    obtain ⟨j, hj, e⟩ := hPk S (Abelian.monoLift p (q ≫ kernel.ι h) h₁') inferInstance hS
    exact ⟨j, by omega, e⟩
  · have := hS.mono_of_ne_zero hQ _ h₁
    have h₃ : kernel.ι h ≫ cokernel.π p ≫ cokernel.π g = 0 := kernel.condition h
    have h₂ : (q ≫ kernel.ι h ≫ cokernel.π p) ≫ cokernel.π g = 0 := by
      rw [Category.assoc, Category.assoc, h₃, comp_zero]
    have : Mono (Abelian.monoLift g _ h₂) := mono_of_mono_fac (Abelian.monoLift_comp g _ h₂)
    have : IsIso (Abelian.monoLift g _ h₂) :=
      ((hT k).2.2 S _ inferInstance hS.1).resolve_left hS.2.1
    exact ⟨k, Nat.lt_succ_self k, ⟨asIso (Abelian.monoLift g _ h₂)⟩⟩

/-- **Irreducible lisse subsheaves are finite up to isomorphism.** Among infinitely many
irreducible lisse subsheaves `T₀, T₁, …` of a lisse sheaf `V`, two are isomorphic: otherwise the
sums `T₀ + ⋯ + T_{k-1} ⊆ V` would have rank at least `k` for every `k`. -/
theorem IsAdicLisseSheaf.exists_iso_of_mono [IsLocallyNoetherian Y] (hM : M.IsEquivalenceAt t)
    {V : AdicSheaf l Y} (hV : IsAdicLisseSheaf V) (T : ℕ → AdicSheaf l Y)
    (hT : ∀ j, IsIrreducibleAdicLocalSystem (T j)) (ι : ∀ j, T j ⟶ V) [∀ j, Mono (ι j)] :
    ∃ a b, a < b ∧ Nonempty (T b ≅ T a) := by
  have key (k : ℕ) : (∃ a b, a < b ∧ Nonempty (T b ≅ T a)) ∨
      ∃ (P : AdicSheaf l Y) (p : P ⟶ V), Mono p ∧ IsAdicLisseSheaf P ∧
        k ≤ adicStalkRank t P ∧ ∀ (S : AdicSheaf l Y) (q : S ⟶ P), Mono q →
          IsIrreducibleAdicLocalSystem S → ∃ j < k, Nonempty (S ≅ T j) := by
    induction k with
    | zero =>
      exact Or.inr ⟨0, 0, inferInstance, IsAdicLisseSheaf.of_isZero (isZero_zero _),
        Nat.zero_le _, fun S q _ hS ↦ absurd (IsZero.of_mono q (isZero_zero _)) hS.2.1⟩
    | succ k ih =>
      obtain h | ⟨P, p, hp, hP, hk, hPk⟩ := ih
      · exact Or.inl h
      obtain ⟨j, hj, e⟩ | ⟨P', p', hp', hP', hr, hP'k⟩ :=
        hV.exists_iso_or_exists_mono_succ t T hT ι k p hP hPk
      · exact Or.inl ⟨j, k, hj, e⟩
      · have := (hT k).adicStalkRank_pos t hM
        exact Or.inr ⟨P', p', hp', hP', by omega, hP'k⟩
  obtain h | ⟨P, p, hp, hP, hk, -⟩ := key (adicStalkRank t V + 1)
  · exact h
  · have := adicStalkRank_le_of_mono t hP hV p
    omega

end Rank

end AlgebraicGeometry.ProEtale
