/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.IrreducibleLisse

/-!
# Pairwise distinct irreducible quotients of a lisse sheaf

On an irreducible scheme `Y`, a lisse sheaf `X` with nonzero morphisms `X ⟶ Sᵢ` to `n` pairwise
non-isomorphic irreducible local systems `S₀, …, S_{n-1}` has rank at least `n`
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.le_finrank_of_ne_zero`). The last morphism is an
epimorphism onto the irreducible `S_{n-1}`; its kernel `K` is lisse and still maps nonzero to every
other `Sᵢ`, since a morphism vanishing on `K` factors through `X / K ≅ S_{n-1}`, and a nonzero
morphism `S_{n-1} ⟶ Sᵢ` would be an isomorphism. The rank of `X` is that of `K` plus at least
one.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}} [IrreducibleSpace Y]

/-- A nonzero morphism from a lisse sheaf to an irreducible local system on an irreducible scheme
is an epimorphism: its image is a nonzero lisse subsheaf. -/
theorem IsIrreducibleAdicLocalSystem.epi_of_ne_zero {X S : AdicSheaf l Y}
    (hS : IsIrreducibleAdicLocalSystem S) (hX : IsAdicLisseSheaf X) (p : X ⟶ S) (hp : p ≠ 0) :
    Epi p := by
  have hI : ¬ IsZero (Limits.image p) := fun h ↦ hp (by
    rw [← image.fac p, h.eq_of_tgt (factorThruImage p) 0, zero_comp])
  have := hS.isIso_of_mono (hX.image hS.1 p) hI (image.ι p)
  rw [← image.fac p]
  infer_instance

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- **A lisse sheaf with nonzero morphisms to `n` pairwise non-isomorphic irreducible local
systems has rank at least `n`**, on an irreducible scheme. -/
theorem IsAdicLisseSheaf.le_finrank_of_ne_zero (s : Spec (.of K) ⟶ Y) (n : ℕ) :
    ∀ (S : Fin n → AdicSheaf l Y) (_ : ∀ i, IsIrreducibleAdicLocalSystem (S i))
      (_ : ∀ i j, Nonempty (S i ≅ S j) → i = j) (X : AdicSheaf l Y) (_ : IsAdicLisseSheaf X)
      (p : ∀ i, X ⟶ S i) (_ : ∀ i, p i ≠ 0),
      n ≤ Module.finrank (PadicAlgCl l)
        ((WeilCoefficients.toModuleCat l).obj ((geometricStalkFunctor l s).obj X)) := by
  induction n with
  | zero => intros; exact Nat.zero_le _
  | succ n ih =>
    intro S hS hdist X hX p hp
    set q := p (Fin.last n)
    have : Epi q := (hS _).epi_of_ne_zero hX q (hp _)
    have hK := (hX.kernel_cokernel_of_irreducibleSpace (hS (Fin.last n)).1 q).1
    have hp' (i : Fin n) : kernel.ι q ≫ p i.castSucc ≠ 0 := by
      intro h0
      set g := Abelian.epiDesc q (p i.castSucc) h0
      have hg : q ≫ g = p i.castSucc := Abelian.comp_epiDesc q (p i.castSucc) h0
      have hg0 : g ≠ 0 := fun h ↦ hp i.castSucc (by rw [← hg, h, comp_zero])
      have := (hS _).isIso_of_ne_zero (hS _) g hg0
      exact (Fin.castSucc_lt_last i).ne' (hdist _ _ ⟨asIso g⟩)
    have h₁ := ih (fun i ↦ S i.castSucc) (fun i ↦ hS _)
      (fun i j h ↦ Fin.castSucc_injective _ (hdist _ _ h)) (kernel q) hK
      (fun i ↦ kernel.ι q ≫ p i.castSucc) hp'
    -- the stalk of `X` contains that of `K` in the kernel of the surjection onto that of `S`
    let ω := geometricStalkFunctor l s
    let τ := WeilCoefficients.toModuleCat l
    have := hX.finiteDimensional_geometricStalkFunctor s
    have hinj : Function.Injective (τ.map (ω.map (kernel.ι q))).hom :=
      (ModuleCat.mono_iff_injective _).1 inferInstance
    have hsurj : Function.Surjective (τ.map (ω.map q)).hom := by
      have h := (ModuleCat.epi_iff_surjective _).1 (Functor.map_epi ω q)
      exact h
    have hle : LinearMap.range (τ.map (ω.map (kernel.ι q))).hom ≤
        LinearMap.ker (τ.map (ω.map q)).hom := by
      rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← τ.map_comp,
        ← ω.map_comp, kernel.condition, ω.map_zero, τ.map_zero]
      rfl
    have hS0 : Module.finrank (PadicAlgCl l) (τ.obj (ω.obj (S (Fin.last n)))) ≠ 0 := fun h ↦
      (hS (Fin.last n)).2.1
        (((hS (Fin.last n)).1.isZero_iff_finrank_geometricStalkFunctor_eq_zero s).2 h)
    have hrk := LinearMap.finrank_range_add_finrank_ker (τ.map (ω.map q)).hom
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at hrk
    have h₂ := Submodule.finrank_mono hle
    rw [LinearMap.finrank_range_of_inj hinj] at h₂
    have h₃ : n + 1 ≤ Module.finrank (PadicAlgCl l) (τ.obj (ω.obj (kernel q))) +
        Module.finrank (PadicAlgCl l) (τ.obj (ω.obj (S (Fin.last n)))) := by
      have : n ≤ Module.finrank (PadicAlgCl l) (τ.obj (ω.obj (kernel q))) := h₁
      omega
    calc n + 1 ≤ _ := h₃
      _ ≤ Module.finrank (PadicAlgCl l) (LinearMap.ker (τ.map (ω.map q)).hom) +
          Module.finrank (PadicAlgCl l) (τ.obj (ω.obj (S (Fin.last n)))) :=
        Nat.add_le_add_right h₂ _
      _ = _ := by rw [add_comm]; exact hrk

omit [IrreducibleSpace Y] [IsAlgClosed K] in
/-- The stalk of a pullback `g^* M` at a geometric point `s` is the stalk of `M` at `s ≫ g`. -/
theorem finrank_geometricStalkFunctor_upperStar {Z : Scheme.{u}} (g : Y ⟶ Z) (M : AdicSheaf l Z)
    (s : Spec (.of K) ⟶ Y) :
    Module.finrank (PadicAlgCl l)
        ((WeilCoefficients.toModuleCat l).obj ((geometricStalkFunctor l s).obj ((g)^*ᵃ[l].obj M))) =
      Module.finrank (PadicAlgCl l)
        ((WeilCoefficients.toModuleCat l).obj ((geometricStalkFunctor l (s ≫ g)).obj M)) :=
  ((AdicSheaf.forget _ ⋙ Sheaf.Γ _ _ ⋙ WeilCoefficients.toModuleCat l).mapIso
    ((adicUpperStarComp l s g).app M)).toLinearEquiv.finrank_eq.symm

/-- **A lisse sheaf of rank one is an irreducible local system**, on an irreducible scheme: a
nonzero lisse subsheaf has rank one as well, so it is everything. -/
theorem IsAdicLisseSheaf.isIrreducibleAdicLocalSystem_of_finrank_eq_one {H : AdicSheaf l Y}
    (hH : IsAdicLisseSheaf H) (s : Spec (.of K) ⟶ Y)
    (h1 : Module.finrank (PadicAlgCl l)
      ((WeilCoefficients.toModuleCat l).obj ((geometricStalkFunctor l s).obj H)) = 1) :
    IsIrreducibleAdicLocalSystem H := by
  refine ⟨hH, fun h ↦ ?_, fun A j _ hA ↦ ?_⟩
  · rw [(hH.isZero_iff_finrank_geometricStalkFunctor_eq_zero s).1 h] at h1
    exact zero_ne_one h1
  have hle := finrank_geometricStalkFunctor_le_of_mono hH j s
  rw [h1] at hle
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle with h | h
  · exact Or.inl ((hA.isZero_iff_finrank_geometricStalkFunctor_eq_zero s).2 h)
  · exact Or.inr (hA.isIso_of_mono_of_finrank_eq hH j s (h.trans h1.symm))

end AlgebraicGeometry.ProEtale
