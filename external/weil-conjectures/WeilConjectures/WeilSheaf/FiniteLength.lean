/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.AbelianIrreducible
public import WeilConjectures.WeilSheaf.LisseFiltration

/-!
# Lisse Weil sheaves have finite length

Let `X` be a `k₀`-scheme whose geometric fiber `X̄` is irreducible, for instance a smooth
geometrically connected curve. Kernels and cokernels of morphisms of lisse Weil sheaves on `X`
are lisse, and a nonzero lisse Weil sheaf has a nonzero stalk at every closed point. Hence a
proper nonzero lisse subsheaf of a lisse sheaf `F` and the corresponding quotient have smaller
rank, and induction on the rank shows that `F` has finite length in the category of lisse Weil
sheaves: it is built from irreducible lisse sheaves by finitely many extensions.

## Main statements

- `AlgebraicGeometry.WeilSheaf.IsLisse.kernel` and `AlgebraicGeometry.WeilSheaf.IsLisse.cokernel`:
  lisse sheaves are closed under kernels and cokernels.
- `AlgebraicGeometry.WeilSheaf.IsLisse.nontrivial_stalk`: nonzero lisse sheaves have nonzero
  stalks.
- `AlgebraicGeometry.WeilSheaf.IsLisse.induction_on_shortExact`
(`theorem-weight-bound-affine-line`): the
  finite length of lisse Weil sheaves, as an induction principle.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [IrreducibleSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]

/-- The cokernel of a morphism of lisse Weil sheaves is lisse, the geometric fiber being
irreducible. -/
theorem IsLisse.cokernel {F G : WeilSheaf k₀ l X} (hF : F.IsLisse) (hG : G.IsLisse)
    (f : F ⟶ G) : (cokernel f).IsLisse :=
  ((ProEtale.isAdicLisseSheaf_kernel_cokernel_of_irreducibleSpace hF hG
    ((carrierFunctor k₀ l X).map f)).2).of_iso (PreservesCokernel.iso _ f).symm

/-- The kernel of a morphism of lisse Weil sheaves is lisse, the geometric fiber being
irreducible. -/
theorem IsLisse.kernel {F G : WeilSheaf k₀ l X} (hF : F.IsLisse) (hG : G.IsLisse)
    (f : F ⟶ G) : (kernel f).IsLisse :=
  ((ProEtale.isAdicLisseSheaf_kernel_cokernel_of_irreducibleSpace hF hG
    ((carrierFunctor k₀ l X).map f)).1).of_iso (PreservesKernel.iso _ f).symm

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- A nonzero lisse Weil sheaf has a nonzero stalk at every closed point, the geometric fiber
being irreducible. -/
theorem IsLisse.nontrivial_stalk {F : WeilSheaf k₀ l X} (hF : F.IsLisse) (hF0 : ¬ IsZero F)
    (x : X.finitePoints) : Nontrivial (F.stalk x).carrier :=
  have := hF.nontrivial_globalSections_upperStar_of_irreducibleSpace
    (fun h ↦ hF0 (isZero_iff_isZero_carrier.2 h)) (AlgebraicClosure k₀)
    ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x)
  this

/-- The rank of a Weil sheaf at a closed point: the dimension of its geometric stalk. -/
noncomputable abbrev finrankStalk (F : WeilSheaf k₀ l X) (x : X.finitePoints) : ℕ :=
  Module.finrank (PadicAlgCl l) (F.stalk x).carrier

omit [IrreducibleSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber] in
/-- A proper subobject of a Weil sheaf whose cokernel has a nonzero stalk at `x` has smaller
rank at `x`. -/
theorem finrankStalk_lt_of_mono {G F : WeilSheaf k₀ l X} (i : G ⟶ F) [Mono i] (x : X.finitePoints)
    (hQ : Nontrivial ((cokernel i).stalk x).carrier) : G.finrankStalk x < F.finrankStalk x := by
  let s := (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x
  let m := (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1
  have hs := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
    (X ↘ Spec (CommRingCat.of k₀)) x
  let a := stalkAtMap s m hs i
  let b := stalkAtMap s m hs (cokernel.π i)
  have ha : Function.Injective a := injective_stalkAtMap s m hs i
  have hb : Function.Surjective b := surjective_stalkAtMap s m hs (cokernel.π i)
  have hab : LinearMap.range a ≤ LinearMap.ker b := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    change stalkAtMap s m hs (cokernel.π i) (stalkAtMap s m hs i y) = 0
    rw [← stalkAtMap_comp, cokernel.condition, stalkAtMap_zero]
  have hker : LinearMap.ker b ≠ ⊤ := by
    intro h
    obtain ⟨z, hz⟩ := exists_ne (0 : ((cokernel i).stalk x).carrier)
    obtain ⟨y, rfl⟩ := hb z
    exact hz (LinearMap.mem_ker.1 (h ▸ Submodule.mem_top))
  calc G.finrankStalk x = Module.finrank _ (LinearMap.range a) :=
        (LinearMap.finrank_range_of_inj ha).symm
    _ ≤ Module.finrank _ (LinearMap.ker b) := Submodule.finrank_mono hab
    _ < F.finrankStalk x := Submodule.finrank_lt hker

omit [IrreducibleSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber] in
/-- The cokernel of a monomorphism from a sheaf with a nonzero stalk at `x` has smaller rank at
`x`. -/
theorem finrankStalk_cokernel_lt {G F : WeilSheaf k₀ l X} (i : G ⟶ F) [Mono i]
    (x : X.finitePoints) (hG : Nontrivial (G.stalk x).carrier) :
    (cokernel i).finrankStalk x < F.finrankStalk x := by
  let s := (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x
  let m := (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1
  have hs := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
    (X ↘ Spec (CommRingCat.of k₀)) x
  let a := stalkAtMap s m hs i
  let b := stalkAtMap s m hs (cokernel.π i)
  have ha : Function.Injective a := injective_stalkAtMap s m hs i
  have hb : Function.Surjective b := surjective_stalkAtMap s m hs (cokernel.π i)
  have hker : LinearMap.ker b ≠ ⊥ := by
    intro h
    obtain ⟨y, hy⟩ := exists_ne (0 : (G.stalk x).carrier)
    have : a y ∈ LinearMap.ker b := by
      rw [LinearMap.mem_ker]
      change stalkAtMap s m hs (cokernel.π i) (stalkAtMap s m hs i y) = 0
      rw [← stalkAtMap_comp, cokernel.condition, stalkAtMap_zero]
    rw [h, Submodule.mem_bot] at this
    exact hy (ha (this.trans (map_zero a).symm))
  have h := LinearMap.finrank_range_add_finrank_ker b
  have h2 : Module.finrank (PadicAlgCl l) (LinearMap.range b) = (cokernel i).finrankStalk x := by
    rw [LinearMap.range_eq_top.2 hb, finrank_top]
    rfl
  have h3 : F.finrankStalk x = Module.finrank (PadicAlgCl l) (F.stalkAt s m hs).carrier := rfl
  have hpos : 0 < Module.finrank (PadicAlgCl l) (LinearMap.ker b) :=
    Module.finrank_pos_iff.2 (Submodule.nontrivial_iff_ne_bot.2 hker)
  omega

/-- **Finite length of lisse Weil sheaves.** If the geometric fiber of `X` is irreducible, for
instance if `X` is a smooth geometrically connected curve, then every lisse Weil sheaf `F` on `X`
has finite length in the category of lisse Weil sheaves: there is a finite filtration
`0 = F₀ ⊂ F₁ ⊂ ⋯ ⊂ Fₘ = F` by lisse Weil subsheaves whose graded pieces are irreducible lisse.
This is stated as the corresponding induction principle: a property of lisse sheaves which holds
for zero and irreducible lisse sheaves and is stable under extensions of lisse sheaves holds
for all lisse sheaves. The proof is the induction on the rank of the blueprint: a nonzero lisse
sheaf which is not irreducible has a proper nonzero lisse subsheaf, whose cokernel is lisse,
and both have smaller rank at any closed point. (blueprint: `theorem-weight-bound-affine-line`) -/
theorem IsLisse.induction_on_shortExact {P : WeilSheaf k₀ l X → Prop}
    (zero : ∀ F : WeilSheaf k₀ l X, IsZero F → P F)
    (irreducible : ∀ F : WeilSheaf k₀ l X, F.IsIrreducibleLisse → P F)
    (extension : ∀ S : ShortComplex (WeilSheaf k₀ l X), S.ShortExact → S.X₁.IsLisse →
      S.X₂.IsLisse → S.X₃.IsLisse → P S.X₁ → P S.X₃ → P S.X₂)
    {F : WeilSheaf k₀ l X} (hF : F.IsLisse) : P F := by
  by_cases hF0 : IsZero F
  · exact zero F hF0
  obtain ⟨x, -⟩ := F.exists_nontrivial_stalk_of_not_isZero hF0
  suffices key : ∀ n : ℕ, ∀ F : WeilSheaf k₀ l X, F.IsLisse → F.finrankStalk x ≤ n → P F from
    key _ F hF le_rfl
  intro n
  induction n with
  | zero =>
    intro F hF hn
    by_contra hP
    have hF0 : ¬ IsZero F := fun h ↦ hP (zero F h)
    have := hF.nontrivial_stalk hF0 x
    have : 0 < F.finrankStalk x := Module.finrank_pos
    omega
  | succ n ih =>
    intro F hF hn
    by_cases hF0 : IsZero F
    · exact zero F hF0
    by_cases hirr : F.IsIrreducibleLisse
    · exact irreducible F hirr
    obtain ⟨G, i, hi, hG, hG0, hiso⟩ : ∃ (G : WeilSheaf k₀ l X) (i : G ⟶ F), Mono i ∧
        G.IsLisse ∧ ¬ IsZero G ∧ ¬ IsIso i := by
      by_contra h
      push Not at h
      exact hirr ⟨hF, hF0, fun G i hi hG ↦ by
        by_cases hG0 : IsZero G
        · exact Or.inl hG0
        · exact Or.inr (h G i hi hG hG0)⟩
    have hQ : (Limits.cokernel i).IsLisse := hG.cokernel hF i
    have hQ0 : ¬ IsZero (Limits.cokernel i) := fun h ↦ by
      have : Epi i := Preadditive.epi_of_cokernel_zero (h.eq_of_tgt _ _)
      exact hiso (isIso_of_mono_of_epi i)
    have hS : (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i))
        hi (inferInstanceAs (Epi (cokernel.π i)))
    refine extension _ hS hG hF hQ ?_ ?_
    · exact ih G hG (Nat.lt_succ_iff.1
        ((finrankStalk_lt_of_mono i x (hQ.nontrivial_stalk hQ0 x)).trans_le hn))
    · exact ih _ hQ (Nat.lt_succ_iff.1
        ((finrankStalk_cokernel_lt i x (hG.nontrivial_stalk hG0 x)).trans_le hn))

end AlgebraicGeometry.WeilSheaf
