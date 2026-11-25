/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.ConstantTowerStandardization
public import WeilConjectures.LinearAlgebra.Basis.PowQuotientTower
public import WeilConjectures.SixFunctors.ProEtale.DisjointOpensGluing
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LocallyConstantWContractible

/-!
# Simultaneous trivialisation of towers of locally constant sheaves on w-contractible objects

Let `L` be a tower of étale sheaves of `Λ`-modules on `S` with epimorphic transitions, each `Lₙ`
étale-locally isomorphic to a finite module `Mₙ`, and `W ≅ Spec R` an object of `S_proét` with
`R` w-contractible.

- `AlgebraicGeometry.Scheme.ProEt.hasDisjointRefinements`: the pro-étale site of `Spec R` has
  disjoint refinements;
- `AlgebraicGeometry.ProEtale.nonempty_iso_constantSheaf_upperStar_comparisonUpperStar`:
  `W^* ν^* Lₙ ≅ (Mₙ)_W` for each `n`;
- `ProEtale.nonempty_iso_ofOpSequence_constantSheaf_upperStar_comparisonUpperStar`:
  if every surjection `Mₙ₊₁ ⟶ Mₙ` is a standard `stdₙ` up to automorphism, the tower
  `W^* ν^* Lₙ` is isomorphic to the standard tower `((Mₙ)_W, stdₙ)`, simultaneously for all `n`;
- `AlgebraicGeometry.ProEtale.nonempty_iso_powQuotientTower_upperStar_comparisonUpperStar`: the
  case of étale-locally free `Λ ⧸ Iⁿ⁺¹`-modules of rank `r` (e.g. `𝒪_E ⧸ ℓⁿ⁺¹`), where the
  standard tower has the reduction maps.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-- The pro-étale site of the spectrum of a w-contractible ring has disjoint refinements: every
covering sieve of the terminal object contains a cover by pairwise disjoint opens. -/
theorem Scheme.ProEt.hasDisjointRefinements {Y : Scheme.{u}} {R : CommRingCat.{u}}
    [IsWContractibleRing R] (e : Y ≅ Spec R) :
    (ProEt.topology Y).HasDisjointRefinements.{u} (ProEt.mk (𝟙 Y)) := by
  intro S hS
  obtain ⟨κ, V, v, s, hs, hSv⟩ := exists_comp_sigmaDesc_eq_id_of_forall_exists_retraction
    (fun T _ _ _ _ ↦ IsWContractibleRing.exists_retraction R T) (W := ProEt.mk (𝟙 Y)) e hS
  obtain ⟨ι, U, f, hcov, hSf, hmono, hdisj⟩ :=
    exists_disjoint_cover_of_comp_sigmaDesc_eq_id v s hs S hSv
  exact ⟨ι, U, f, ⟨hmono, fun i j hij _ a b h ↦ hdisj i j hij _ a b h⟩, hcov, hSf⟩

namespace ProEtale

open ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- If `u^* F ≅ M_U` for an étale `u : U ⟶ S`, then `z^* ν^* F ≅ M_Z` for every `z = b ≫ u`. -/
noncomputable def upperStarComparisonUpperStarIsoOfFactor {S U Z : Scheme.{u}} (u : U ⟶ S)
    (b : Z ⟶ U) (z : Z ⟶ S) (hz : b ≫ u = z) (F : Sheaf S.smallEtaleTopology A) {M : A}
    (e : (Etale.upperStar A u).obj F ≅ (constantSheaf U.smallEtaleTopology A).obj M) :
    (ProEtale.upperStar A z).obj ((comparisonUpperStar A S).obj F) ≅
      (constantSheaf (Scheme.ProEt.topology Z) A).obj M :=
  (ProEtale.upperStarCongr A hz.symm).app _ ≪≫
    (ProEtale.upperStarComp A b u).app _ ≪≫
    (ProEtale.upperStar A b).mapIso ((comparisonUpperStarCompUpperStarIso A u).app F ≪≫
      (comparisonUpperStar A U).mapIso e ≪≫
      (constantSheafCompComparisonUpperStarIso A U).app M) ≪≫
    (constantSheafCompUpperStarIso A b).app M

/-- **Trivialisation with a prescribed value on a w-contractible object.** If `F` is an étale
sheaf on `S` with `uᵢ^* F ≅ M` for a jointly surjective étale family `uᵢ`, and `W` is an object
of `S_proét` with `W ≅ Spec R`, `R` w-contractible, then `W^* ν^* F ≅ M` on `W_proét`: it is so
on the pieces of a decomposition of `W` into disjoint opens, which glue. -/
theorem nonempty_iso_constantSheaf_upperStar_comparisonUpperStar {S : Scheme.{u}} {ι : Type u}
    {U : ι → Scheme.{u}} (u : ∀ i, U i ⟶ S) [∀ i, Etale (u i)]
    (hu : ∀ x, ∃ i, x ∈ Set.range (u i)) (F : Sheaf S.smallEtaleTopology A) (M : A)
    (hF : ∀ i, Nonempty ((Etale.upperStar A (u i)).obj F ≅
      (constantSheaf (U i).smallEtaleTopology A).obj M))
    (W : S.ProEt) {R : CommRingCat.{u}} [IsWContractibleRing R] (e : W.left ≅ Spec R) :
    Nonempty ((ProEtale.upperStar A W.hom).obj ((comparisonUpperStar A S).obj F) ≅
      (constantSheaf (Scheme.ProEt.topology W.left) A).obj M) := by
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
  have hj (j : κ) : Nonempty (((O j).ι)^*[A].obj ((W.hom)^*[A].obj
      ((comparisonUpperStar A S).obj F)) ≅
        (constantSheaf (Scheme.ProEt.topology (O j)) A).obj M) := by
    obtain ⟨Y, a, _, ⟨i⟩, hfac⟩ := hO j
    have hb : a.left ≫ u i = (O j).ι ≫ W.hom := congrArg (fun φ ↦ φ.left) hfac
    exact ⟨((ProEtale.upperStarComp A (O j).ι W.hom).app _).symm ≪≫
      upperStarComparisonUpperStarIsoOfFactor A (u i) a.left _ hb F (hF i).some⟩
  exact ProEtale.nonempty_iso_constantSheaf_of_disjoint_opens A O hdisj hcov _ M
    fun j ↦ (hj j).some

/-- **Simultaneous standard trivialisation of a tower on a w-contractible object.** Let `L` be a
tower of étale sheaves of `Λ`-modules on `S` with epimorphic transitions, where each `Lₙ` is
étale-locally isomorphic to the constant sheaf at a finite module `Mₙ`, and every surjection
`Mₙ₊₁ ⟶ Mₙ` is the standard map `stdₙ` up to an automorphism of `Mₙ₊₁` (e.g. free modules of
constant rank over `𝒪_E ⧸ ℓⁿ`, `Module.Basis.exists_basis_map_eq`). Then for every object
`W ≅ Spec R` of `S_proét`, `R` w-contractible, the tower `W^* ν^* Lₙ` is isomorphic to the
standard tower of constant sheaves `(Mₙ, stdₙ)`, simultaneously for all `n`. -/
theorem nonempty_iso_ofOpSequence_constantSheaf_upperStar_comparisonUpperStar
    {Λ : Type (u + 1)} [CommRing Λ] {S : Scheme.{u}}
    (L : ℕᵒᵖ ⥤ Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hL : ∀ n : ℕ, Epi (L.map (homOfLE (n.le_add_right 1)).op))
    (M : ℕ → ModuleCat.{u + 1} Λ) [∀ n, Module.Finite Λ (M n)] (std : ∀ n, M (n + 1) ⟶ M n)
    (hstd : ∀ n (f : M (n + 1) ⟶ M n), Function.Surjective f →
      ∃ g : M (n + 1) ≅ M (n + 1), g.hom ≫ f = std n)
    (htriv : ∀ n, ∃ (ι : Type u) (U : ι → Scheme.{u}) (u : ∀ i, U i ⟶ S),
      (∀ i, Etale (u i)) ∧ (∀ x, ∃ i, x ∈ Set.range (u i)) ∧
      ∀ i, Nonempty ((Etale.upperStar _ (u i)).obj (L.obj (op n)) ≅
        (constantSheaf (U i).smallEtaleTopology _).obj (M n)))
    (W : S.ProEt) {R : CommRingCat.{u}} [IsWContractibleRing R] (e : W.left ≅ Spec R) :
    Nonempty (L ⋙ comparisonUpperStar _ S ⋙ ProEtale.upperStar _ W.hom ≅
      Functor.ofOpSequence (X := fun n ↦ (constantSheaf (Scheme.ProEt.topology W.left) _).obj
        (M n)) fun n ↦ (constantSheaf _ _).map (std n)) := by
  have hiso (n : ℕ) : Nonempty ((ProEtale.upperStar _ W.hom).obj
      ((comparisonUpperStar _ S).obj (L.obj (op n))) ≅
        (constantSheaf (Scheme.ProEt.topology W.left) _).obj (M n)) := by
    obtain ⟨ι, U, u, hu, hcov, hU⟩ := htriv n
    exact nonempty_iso_constantSheaf_upperStar_comparisonUpperStar _ u hcov _ (M n) hU W e
  have := (comparisonAdjunction (ModuleCat.{u + 1} Λ) S).isLeftAdjoint
  have := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) W.hom).isLeftAdjoint
  exact nonempty_iso_ofOpSequence_constantSheaf (Scheme.ProEt.topology W.left)
    (Scheme.ProEt.isTerminalMkId W.left) (Scheme.ProEt.hasDisjointRefinements e) M std hstd _
    (fun n ↦ (hiso n).some) fun n ↦ by
      have := hL n
      dsimp
      infer_instance

/-- **Towers of étale-locally free `Λ ⧸ Iⁿ⁺¹`-modules of rank `r`.** Let `Λ` be a local ring with
a proper ideal `I` (e.g. `𝒪_E` and `ℓ`), and `L` a tower of étale sheaves of `Λ`-modules on `S`
with epimorphic transitions, each `Lₙ` étale-locally isomorphic to `(Λ ⧸ Iⁿ⁺¹)^r`. Then on every
object `W ≅ Spec R` of `S_proét` with `R` w-contractible, the tower `W^* ν^* Lₙ` is isomorphic
to the standard tower of constant sheaves `(Λ ⧸ Iⁿ⁺¹)^r` with the reduction maps. -/
theorem nonempty_iso_powQuotientTower_upperStar_comparisonUpperStar
    {Λ : Type (u + 1)} [CommRing Λ] [IsLocalRing Λ] (I : Ideal Λ) (hI : I ≠ ⊤) (r : ℕ)
    {S : Scheme.{u}} (L : ℕᵒᵖ ⥤ Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hL : ∀ n : ℕ, Epi (L.map (homOfLE (n.le_add_right 1)).op))
    (htriv : ∀ n, ∃ (ι : Type u) (U : ι → Scheme.{u}) (u : ∀ i, U i ⟶ S),
      (∀ i, Etale (u i)) ∧ (∀ x, ∃ i, x ∈ Set.range (u i)) ∧
      ∀ i, Nonempty ((Etale.upperStar _ (u i)).obj (L.obj (op n)) ≅
        (constantSheaf (U i).smallEtaleTopology _).obj
          (ModuleCat.of Λ (Fin r → Λ ⧸ I ^ (n + 1)))))
    (W : S.ProEt) {R : CommRingCat.{u}} [IsWContractibleRing R] (e : W.left ≅ Spec R) :
    Nonempty (L ⋙ comparisonUpperStar _ S ⋙ ProEtale.upperStar _ W.hom ≅
      Functor.ofOpSequence (X := fun n ↦ (constantSheaf (Scheme.ProEt.topology W.left) _).obj
        (ModuleCat.of Λ (Fin r → Λ ⧸ I ^ (n + 1)))) fun n ↦
          (constantSheaf _ _).map (ModuleCat.ofHom (I.powQuotientReduction r n))) := by
  refine nonempty_iso_ofOpSequence_constantSheaf_upperStar_comparisonUpperStar L hL
    (fun n ↦ ModuleCat.of Λ (Fin r → Λ ⧸ I ^ (n + 1)))
    (fun n ↦ ModuleCat.ofHom (I.powQuotientReduction r n)) (fun n f hf ↦ ?_) htriv W e
  obtain ⟨g, hg⟩ := I.exists_linearEquiv_comp_eq_powQuotientReduction r hI n f.hom hf
  exact ⟨g.toModuleIso, ModuleCat.hom_ext hg⟩

end ProEtale

end AlgebraicGeometry
