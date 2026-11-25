/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections

/-!
# Comparison pullbacks of locally constant sheaves on w-contractible objects

Let `F` be an étale sheaf on `S` trivialised by a jointly surjective family of étale morphisms
`uᵢ : Uᵢ ⟶ S`, that is `uᵢ^* F` is constant.

- `AlgebraicGeometry.ProEtale.isConstant_upperStar_comparisonUpperStar_obj`: for any `z : Z ⟶ S`
  factoring through some `uᵢ`, `z^* ν^* F` is a constant pro-étale sheaf.
- `AlgebraicGeometry.ProEtale.exists_disjoint_opens_isConstant_comparisonUpperStar`: an object
  `W` of `S_proét` whose underlying scheme is the spectrum of a w-contractible ring is covered by
  pairwise disjoint open subschemes on each of which `ν^* F` is constant, since the pulled-back
  étale cover of `W` has a section.

For a tower `(Lₙ)` of finite locally constant sheaves trivialised by one common étale family,
the same disjoint cover of `W` trivialises all the `ν^* Lₙ` at once; since such `W` cover
`S_proét` (`AlgebraicGeometry.Scheme.ProEt.exists_isWContractibleRing_cover`), this is the
first step towards describing `lim ν^* Lₙ` locally as `C(-, lim Mₙ)`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- **Comparison pullbacks of étale-locally constant sheaves are constant where trivialised.**
Let `F` be an étale sheaf on `S` whose pullback to an étale `u : U ⟶ S` is constant. For any
morphism `z : Z ⟶ S` factoring as `b ≫ u`, the pullback of the comparison pullback `ν^* F`
along `z` is a constant pro-étale sheaf: `z^* ν^* F ≅ b^* u^* ν^* F ≅ b^* ν^* (u^* F)` and the
pullbacks of constant sheaves are constant. -/
lemma isConstant_upperStar_comparisonUpperStar_obj {S U Z : Scheme.{u}} (u : U ⟶ S)
    (b : Z ⟶ U) (z : Z ⟶ S) (hz : b ≫ u = z) (F : Sheaf S.smallEtaleTopology A)
    (hF : ((Etale.upperStar A u).obj F).IsConstant U.smallEtaleTopology) :
    ((ProEtale.upperStar A z).obj ((comparisonUpperStar A S).obj F)).IsConstant
      (Scheme.ProEt.topology Z) := by
  obtain ⟨M, ⟨e⟩⟩ := Sheaf.IsConstant.mem_essImage (J := U.smallEtaleTopology)
    (F := (Etale.upperStar A u).obj F)
  refine Sheaf.isConstant_of_iso (Scheme.ProEt.topology Z) (X := M) ?_
  exact (ProEtale.upperStarCongr A hz.symm).app _ ≪≫
    (ProEtale.upperStarComp A b u).app _ ≪≫
    (ProEtale.upperStar A b).mapIso ((comparisonUpperStarCompUpperStarIso A u).app F ≪≫
      (comparisonUpperStar A U).mapIso e.symm ≪≫
      (constantSheafCompComparisonUpperStarIso A U).app M) ≪≫
    (constantSheafCompUpperStarIso A b).app M

/-- **Trivialisation on a w-contractible object.** Let `F` be an étale sheaf on `S` trivialised
by a jointly surjective family of étale morphisms `uᵢ : Uᵢ ⟶ S` (each `uᵢ^* F` constant), and
`W` an object of the pro-étale site of `S` whose underlying scheme is the spectrum of a
w-contractible ring. Then `W` is covered by pairwise disjoint open subschemes `Oⱼ` on each of
which the comparison pullback `ν^* F` is constant: the pulled-back étale cover of `W` has a
section, `W` being w-contractible
(`AlgebraicGeometry.Scheme.ProEt.exists_disjoint_opens_of_forall_exists_retraction`). The cover
does not depend on `F` beyond the trivialising family, so for a tower of sheaves trivialised by a
common family it serves all levels at once. -/
theorem exists_disjoint_opens_isConstant_comparisonUpperStar {S : Scheme.{u}} {ι : Type u}
    {U : ι → Scheme.{u}} (u : ∀ i, U i ⟶ S) [∀ i, Etale (u i)]
    (hu : ∀ x, ∃ i, x ∈ Set.range (u i)) (F : Sheaf S.smallEtaleTopology A)
    (hF : ∀ i, ((Etale.upperStar A (u i)).obj F).IsConstant (U i).smallEtaleTopology)
    (W : S.ProEt) {R : CommRingCat.{u}} [IsWContractibleRing R] (e : W.left ≅ Spec R) :
    ∃ (κ : Type u) (O : κ → W.left.Opens), (∀ i j, i ≠ j → Disjoint (O i) (O j)) ∧
      (∀ x, ∃ i, x ∈ O i) ∧ ∀ j, ((ProEtale.upperStar A ((O j).ι ≫ W.hom)).obj
        ((comparisonUpperStar A S).obj F)).IsConstant (Scheme.ProEt.topology (O j)) := by
  -- the étale cover, as a covering sieve of the terminal object of `S_proét`
  let T₀ : S.ProEt := Scheme.ProEt.mk (𝟙 S)
  let V (i : ι) : S.ProEt := Scheme.ProEt.mk (u i)
  let v (i : ι) : V i ⟶ T₀ := MorphismProperty.Over.homMk (u i)
  have hR₀ : Sieve.ofArrows V v ∈ Scheme.ProEt.topology S T₀ := by
    rw [Scheme.ProEt.mem_topology_iff]
    refine ⟨Presieve.ofArrows V v, ?_, Sieve.le_generate _⟩
    rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    refine Scheme.etalePrecoverage_le_proetalePrecoverage _ ?_
    rw [Scheme.etalePrecoverage, Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨hu, fun i ↦ inferInstanceAs (Etale (u i))⟩
  let t : W ⟶ T₀ := MorphismProperty.Over.homMk W.hom
  have hR := (Scheme.ProEt.topology S).pullback_stable t hR₀
  obtain ⟨κ, O, hdisj, hcov, hO⟩ :=
    Scheme.ProEt.exists_disjoint_opens_of_forall_exists_retraction
      (fun T _ _ _ _ ↦ IsWContractibleRing.exists_retraction R T) e hR
  refine ⟨κ, O, hdisj, hcov, fun j ↦ ?_⟩
  obtain ⟨Y, a, _, ⟨i⟩, hfac⟩ := hO j
  have hb : a.left ≫ u i = (O j).ι ≫ W.hom := congrArg (fun φ ↦ φ.left) hfac
  exact isConstant_upperStar_comparisonUpperStar_obj A (u i) a.left _ hb F (hF i)

end AlgebraicGeometry.ProEtale
