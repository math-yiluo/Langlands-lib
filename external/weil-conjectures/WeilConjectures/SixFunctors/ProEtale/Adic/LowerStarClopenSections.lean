/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.Module
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClopenIdempotent

/-!
# Pushforward along a morphism with a clopen partition into sections is exact

Let `g : Y ⟶ S` be a morphism of schemes and `s₁, …, sₙ : S ⟶ Y` sections of `g` which are open
immersions with closed, pairwise disjoint ranges covering `Y`; for instance `Y = ⊔ᵢ S`. Then the
pushforward `g_*` of pro-étale sheaves is exact: the idempotents `e_{sᵢ}` of the clopen
subschemes (`AlgebraicGeometry.ProEtale.clopenIdempotentSheaf`) sum to the identity, and each
factors through `sᵢ_* sᵢ^*`, while `g_* sᵢ_* sᵢ^* ≅ (sᵢ ≫ g)_* sᵢ^* ≅ sᵢ^*` is exact.

## Main results

- `CategoryTheory.Functor.preservesEpimorphisms_of_sum_comp_eq_id`: an additive functor `F`
  preserves epimorphisms if the identity is a finite sum of composites `𝟭 ⟶ Tᵢ ⟶ 𝟭` with every
  `Tᵢ ⋙ F` preserving epimorphisms.
- `AlgebraicGeometry.ProEtale.preservesFiniteColimits_lowerStar_of_sections`: the pushforward
  `g_*` is exact.
- `AlgebraicGeometry.ProEtale.preservesFiniteColimits_adicLowerStar_of_sections`: the same for
  sheaves of modules over the constant `ℓ`-adic sheaves.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]

/-- An additive functor `F` preserves epimorphisms if the identity of its source is a finite sum
`∑ᵢ ηᵢ ≫ ψᵢ` of composites `𝟭 ⟶ Tᵢ ⟶ 𝟭` with every `Tᵢ ⋙ F` preserving epimorphisms. -/
lemma preservesEpimorphisms_of_sum_comp_eq_id {ι : Type*} [Fintype ι] (F : C ⥤ D)
    [F.Additive] (T : ι → C ⥤ C) (η : ∀ i, 𝟭 C ⟶ T i) (ψ : ∀ i, T i ⟶ 𝟭 C)
    (h : ∑ i, η i ≫ ψ i = 𝟙 _) [∀ i, (T i ⋙ F).PreservesEpimorphisms] :
    F.PreservesEpimorphisms where
  preserves {G G'} α _ := by
    refine Preadditive.epi_of_cancel_zero _ fun {Z} c hc ↦ ?_
    have key (i : ι) : F.map ((ψ i).app G') ≫ c = 0 := by
      rw [← cancel_epi ((T i ⋙ F).map α), comp_zero, Functor.comp_map, ← F.map_comp_assoc,
        (ψ i).naturality, Functor.id_map, F.map_comp_assoc, hc, comp_zero]
    have h' := congrArg (fun τ ↦ F.map (τ.app G') ≫ c) h
    simp only [NatTrans.app_sum, NatTrans.comp_app, F.map_sum, Preadditive.sum_comp,
      F.map_comp, Category.assoc, key, comp_zero, Finset.sum_const_zero, NatTrans.id_app,
      F.map_id, Category.id_comp] at h'
    exact h'.symm

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {ι : Type*} [Finite ι] {Y S : Scheme.{u}} (g : Y ⟶ S) (s : ι → (S ⟶ Y))
  [∀ i, IsOpenImmersion (s i)]

/-- For a section `s` of `g` which is an open immersion, `g_* s_* s^* ≅ s^*`. -/
noncomputable def upperStarCompLowerStarCompLowerStarIsoOfComp (t : S ⟶ Y) (ht : t ≫ g = 𝟙 S) :
    ((t)^*[A] ⋙ (t)_*[A]) ⋙ (g)_*[A] ≅ (t)^*[A] :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
    (lowerStarComp A t g ≪≫ lowerStarCongr A ht ≪≫ lowerStarId A S) ≪≫ Functor.rightUnitor _

/-- **Pushforward along a clopen partition into sections preserves epimorphisms.** If the
sections `sᵢ` of `g` are open immersions with closed, pairwise disjoint ranges covering `Y`, then
`g_*` preserves epimorphisms. -/
lemma preservesEpimorphisms_lowerStar_of_sections (hs : ∀ i, s i ≫ g = 𝟙 S)
    (hclosed : ∀ i, IsClosed (Set.range (s i).base))
    (hdisj : Pairwise fun i i' ↦ Disjoint (Set.range (s i).base) (Set.range (s i').base))
    (hcover : ⋃ i, Set.range (s i).base = Set.univ) :
    (g)_*[A].PreservesEpimorphisms := by
  let := Fintype.ofFinite ι
  have (i : ι) : (((s i)^*[A] ⋙ (s i)_*[A]) ⋙ (g)_*[A]).PreservesEpimorphisms :=
    Functor.PreservesEpimorphisms.of_iso
      (upperStarCompLowerStarCompLowerStarIsoOfComp A g (s i) (hs i)).symm
  have hiso (i : ι) := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range A (s i)
    (hclosed i)
  exact Functor.preservesEpimorphisms_of_sum_comp_eq_id (g)_*[A]
    (fun i ↦ (s i)^*[A] ⋙ (s i)_*[A]) (fun i ↦ (upperStarLowerStarAdjunction A (s i)).unit)
    (fun i ↦ Functor.whiskerLeft (s i)^*[A]
      (@inv _ _ _ _ (openImmersionLowerShriekToLowerStar A (s i)) (hiso i)) ≫
      (openImmersionLowerShriekUpperStarAdjunction A (s i)).counit)
    (sum_clopenIdempotentSheaf A s hclosed hdisj hcover)

/-- **Pushforward along a clopen partition into sections is exact.** If the sections `sᵢ` of `g`
are open immersions with closed, pairwise disjoint ranges covering `Y`, then `g_*` preserves
finite colimits. -/
lemma preservesFiniteColimits_lowerStar_of_sections (hs : ∀ i, s i ≫ g = 𝟙 S)
    (hclosed : ∀ i, IsClosed (Set.range (s i).base))
    (hdisj : Pairwise fun i i' ↦ Disjoint (Set.range (s i).base) (Set.range (s i').base))
    (hcover : ⋃ i, Set.range (s i).base = Set.univ) :
    PreservesFiniteColimits (g)_*[A] := by
  have := preservesEpimorphisms_lowerStar_of_sections A g s hs hclosed hdisj hcover
  refine ((Functor.preservesFiniteColimits_tfae (g)_*[A]).out 1 4).1 ?_
  intro T hT
  refine ⟨?_, ?_⟩
  · exact ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono (g)_*[A]).1
      inferInstance T hT).1
  · have := hT.epi_g
    infer_instance

variable (l : ℕ) [Fact l.Prime]

/-- **Pushforward of `ℓ`-adic sheaves along a clopen partition into sections is exact.** If the
sections `sᵢ` of `g` are open immersions with closed, pairwise disjoint ranges covering `Y`, then
`g_*` on sheaves of modules over the constant `ℓ`-adic sheaves preserves finite colimits, as it
does on the underlying sheaves. -/
lemma preservesFiniteColimits_adicLowerStar_of_sections (hs : ∀ i, s i ≫ g = 𝟙 S)
    (hclosed : ∀ i, IsClosed (Set.range (s i).base))
    (hdisj : Pairwise fun i i' ↦ Disjoint (Set.range (s i).base) (Set.range (s i').base))
    (hcover : ⋃ i, Set.range (s i).base = Set.univ) :
    PreservesFiniteColimits (g)_*ᵃ[l] :=
  have := preservesFiniteColimits_lowerStar_of_sections (WeilCoefficients.{u} l) g s hs hclosed
    hdisj hcover
  have : PreservesFiniteColimits ((g)_*ᵃ[l] ⋙ AdicSheaf.forget S) :=
    inferInstanceAs (PreservesFiniteColimits (AdicSheaf.forget Y ⋙ (g)_*[WeilCoefficients.{u} l]))
  preservesFiniteColimits_of_reflects_of_preserves _ (AdicSheaf.forget S)

end AlgebraicGeometry.ProEtale
