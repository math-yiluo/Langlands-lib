/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.SixFunctors.ProEtale.Adic.Module
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!
# The counit of `g^* ⊣ g_*` is an epimorphism for a finite étale `g`

Let `g : Z ⟶ W` be a finite étale morphism of schemes. Since `g` is weakly étale, the pullback
`g^*` on pro-étale sheaves is restriction along the localization functor
(`AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction`), and the counit
`g^* g_* G ⟶ G` evaluates, on sections over `V ∈ Z_proét`, to the restriction of `G` along the
graph `V ⟶ V ×_W Z` of the structure morphism `V ⟶ Z`. This graph is the base change of the
diagonal of `g`, which is both an open immersion (`g` is unramified) and a closed immersion
(`g` is separated). A section of `G` over `V` therefore extends to `V ×_W Z`, by zero on the
open complement of the graph. Hence the counit is surjective on sections, so an epimorphism.

## Main results

- `AlgebraicGeometry.Scheme.ProEt.surjective_map_of_isOpenImmersion_of_isClosed_range`: a sheaf
  of modules on the small pro-étale site is surjective along a morphism whose underlying
  morphism of schemes is an open immersion with closed range.
- `AlgebraicGeometry.ProEtale.epi_upperStarLowerStarAdjunction_counit_app_of_finite_etale`: the
  counit of `g^* ⊣ g_*` on sheaves of `ℚ̄_ℓ`-modules is an epimorphism for `g` finite étale.
- `AlgebraicGeometry.ProEtale.epi_adicUpperStarLowerStarAdjunction_counit_app`: the same for
  sheaves of modules over the constant `ℓ`-adic sheaf.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Scheme.ProEt

/-- **Sections extend along a clopen immersion.** For a sheaf of modules `G` on the small
pro-étale site of `X` and a morphism `i : V ⟶ P` whose underlying morphism of schemes is an
open immersion with closed range, restriction `G(P) ⟶ G(V)` is surjective: a section over `V`
glues with the zero section over the open complement `C` of the range of `i`, since `V` and `C`
form a Zariski cover of `P` whose overlaps over `V × C` are empty. -/
lemma surjective_map_of_isOpenImmersion_of_isClosed_range {R : Type v} [Ring R]
    {X : Scheme.{u}} (G : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) {V P : X.ProEt}
    (i : V ⟶ P) [IsOpenImmersion i.left] (hi : IsClosed (Set.range i.left.base)) :
    Function.Surjective (G.obj.map i.op) := by
  intro s
  let C : P.left.Opens := ⟨(Set.range i.left.base)ᶜ, hi.isOpen_compl⟩
  let c : ofOpenImmersion P C.ι ⟶ P := ofOpenImmersionHom P C.ι
  let π : ∀ k, ![V, ofOpenImmersion P C.ι] k ⟶ P := Fin.cons i (Fin.cons c finZeroElim)
  have hπ (k) : IsOpenImmersion (π k).left :=
    Fin.cases (inferInstanceAs (IsOpenImmersion i.left))
      (Fin.cases (inferInstanceAs (IsOpenImmersion C.ι)) finZeroElim) k
  have hF : Presieve.IsSheaf (topology X) (G.obj ⋙ CategoryTheory.forget (ModuleCat R)) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose _ (CategoryTheory.forget _)).obj G).property
  have hcov : Sieve.generate (Presieve.ofArrows _ π) ∈ topology X P := by
    rw [mem_topology_iff]
    refine ⟨Presieve.ofArrows _ π, ?_, Sieve.le_generate _⟩
    rw [mem_precoverage_iff, Presieve.map_ofArrows]
    refine zariskiPrecoverage_le_proetalePrecoverage _
      ((Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨fun x ↦ ?_, hπ⟩)
    by_cases hx : x ∈ Set.range i.left.base
    · exact ⟨0, hx⟩
    · obtain ⟨y, rfl⟩ : x ∈ Set.range C.ι.base := by
        rw [C.range_ι]
        exact hx
      exact ⟨1, y, rfl⟩
  -- `V` and the complement `C` have empty overlap
  have hempty (T : X.ProEt) (a : T ⟶ V) (b : T ⟶ ofOpenImmersion P C.ι)
      (h : a ≫ i = b ≫ c) :
      IsEmpty T.left := by
    refine ⟨fun t ↦ ?_⟩
    have h' : (b ≫ c).left.base t = (a ≫ i).left.base t := by rw [h]
    have hb : (b ≫ c).left.base t ∈ (C : Set P.left) := by
      rw [← C.range_ι]
      exact ⟨b.left.base t, rfl⟩
    exact hb (by rw [h']; exact ⟨a.left.base t, rfl⟩)
  have hmono (k : Fin 2) {T : X.ProEt} (a b : T ⟶ ![V, ofOpenImmersion P C.ι] k)
      (h : a ≫ π k = b ≫ π k) : a = b := by
    have := hπ k
    refine MorphismProperty.Over.Hom.ext ?_
    exact (cancel_mono (π k).left).1 (congrArg (fun f : T ⟶ P ↦ f.left) h)
  let x : ∀ k, (G.obj ⋙ CategoryTheory.forget _).obj (op (![V, ofOpenImmersion P C.ι] k)) :=
    Fin.cons s (Fin.cons 0 finZeroElim)
  obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 (hF.isSheafFor _ hcov) x
    (fun k k' T a b h ↦ by
      by_cases hkk : k = k'
      · subst hkk
        rw [hmono k a b h]
      · have : IsEmpty T.left := by
          fin_cases k <;> fin_cases k'
          · exact absurd rfl hkk
          · exact hempty T a b h
          · exact hempty T b a h.symm
          · exact absurd rfl hkk
        have := ModuleCat.isZero_iff_subsingleton.1 (isTerminalSectionsOfIsEmpty G T).isZero
        exact @Subsingleton.elim _ this _ _)
  exact ⟨t, ht 0⟩

end Scheme.ProEt

/-- The graph `V ⟶ V ×_W Z` of a morphism `v : V ⟶ Z` over an étale `g : Z ⟶ W` is an open
immersion: it is a base change of the diagonal of `g`, which is an open immersion since `g` is
unramified. -/
lemma isOpenImmersion_pullbackLift_of_etale {Z W V : Scheme.{u}} (g : Z ⟶ W) [Etale g]
    (v : V ⟶ Z) :
    IsOpenImmersion (pullback.lift (𝟙 V) v (by simp) : V ⟶ pullback (v ≫ g) g) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (pullback_lift_diagonal_isPullback v g) inferInstance

/-- The graph `V ⟶ V ×_W Z` of a morphism `v : V ⟶ Z` over a separated `g : Z ⟶ W` is a
closed
immersion: it is a base change of the diagonal of `g`. -/
lemma isClosedImmersion_pullbackLift_of_isSeparated {Z W V : Scheme.{u}} (g : Z ⟶ W)
    [IsSeparated g] (v : V ⟶ Z) :
    IsClosedImmersion (pullback.lift (𝟙 V) v (by simp) : V ⟶ pullback (v ≫ g) g) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (pullback_lift_diagonal_isPullback v g) inferInstance

namespace ProEtale

variable (l : ℕ) [Fact l.Prime] {Z W : Scheme.{u}} (g : Z ⟶ W)

/-- **The counit of `g^* ⊣ g_*` is an epimorphism for a finite étale `g`.** Computing `g^*` by
restriction, the counit restricts sections of `G` along the graphs `V ⟶ V ×_W Z`, which are open
immersions with closed range since `g` is étale and separated; restriction along those is
surjective by `AlgebraicGeometry.Scheme.ProEt.surjective_map_of_isOpenImmersion_of_isClosed_range`.
-/
theorem epi_upperStarLowerStarAdjunction_counit_app_of_finite_etale [IsFinite g] [Etale g]
    (M : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)) :
    Epi ((upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).counit.app M) := by
  rw [← Adjunction.leftAdjointUniq_hom_app_counit _
    (localizationRestrictionLowerStarAdjunction _ g inferInstance)]
  suffices Epi ((localizationRestrictionLowerStarAdjunction (WeilCoefficients.{u} l) g
      inferInstance).counit.app M) from epi_comp _ _
  have : Sheaf.IsLocallySurjective ((localizationRestrictionLowerStarAdjunction
      (WeilCoefficients.{u} l) g inferInstance).counit.app M) := by
    refine Presheaf.isLocallySurjective_of_surjective _ _ fun ⟨V⟩ ↦ ?_
    have : IsOpenImmersion ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
        inferInstance trivial).unit.app V).left := isOpenImmersion_pullbackLift_of_etale g V.hom
    exact Scheme.ProEt.surjective_map_of_isOpenImmersion_of_isClosed_range M
      ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g inferInstance trivial).unit.app V)
      (isClosedImmersion_pullbackLift_of_isSeparated g V.hom).isClosedEmbedding.isClosed_range
  infer_instance

/-- **The counit of `g^* ⊣ g_*` on `ℓ`-adic sheaves is an epimorphism for a finite étale `g`.**
Its underlying morphism of sheaves of `ℚ̄_ℓ`-modules is the counit of
`AlgebraicGeometry.ProEtale.upperStarLowerStarAdjunction`, an epimorphism by
`AlgebraicGeometry.ProEtale.epi_upperStarLowerStarAdjunction_counit_app_of_finite_etale`. -/
theorem epi_adicUpperStarLowerStarAdjunction_counit_app [IsFinite g] [Etale g]
    (M : AdicSheaf l Z) : Epi ((adicUpperStarLowerStarAdjunction l g).counit.app M) := by
  have : Epi ((adicUpperStarLowerStarAdjunction l g).counit.app M).hom := by
    rw [adicUpperStarLowerStarAdjunction, Adjunction.modAdjunction_counit_app_hom]
    exact epi_upperStarLowerStarAdjunction_counit_app_of_finite_etale l g M.X
  have : Epi ((AdicSheaf.forget Z).map ((adicUpperStarLowerStarAdjunction l g).counit.app M)) :=
    this
  exact (AdicSheaf.forget Z).epi_of_epi_map this

end ProEtale

end AlgebraicGeometry
