/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.RingTheory.ProEtale.ClosedLiftRetraction
public import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.Sequence

/-!
# Sections over henselian lifts of weakly contractible objects

Let `X = Spec A`, `i : Z = Spec (A ⧸ I) ⟶ X` and `j : U ⟶ X` a quasi-compact open immersion onto
the complement. Let `C̄` be an ind-étale `A ⧸ I`-algebra all of whose faithfully flat ind-étale
covers split (e.g. a w-contractible one), and `W = Spec H_A(C̄)` its henselian lift
(`Algebra.ClosedLift`). Then:

* every faithfully flat ind-étale cover of `H_A(C̄)` splits
  (`Algebra.ClosedLift.exists_retraction`), so `W` is weakly contractible
  (`AlgebraicGeometry.Scheme.ProEt.isWeaklyContractible_of_forall_exists_retraction`);
* every nonempty clopen subset of `W` meets the closed fibre, so `j_! N` has no sections over
  `W` (`AlgebraicGeometry.ProEtale.subsingleton_openImmersionLowerShriek_closedLiftSpec`);
* consequently the unit `F(W) ⟶ (i^* F)(W ×_X Z)` is bijective
  (`AlgebraicGeometry.ProEtale.bijective_unit_app_closedLiftSpec`), part (1) of blueprint
  `proposition-extension-zero-restriction-closed-subscheme`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable {A : CommRingCat.{u}} (I : Ideal A) (C : Type u) [CommRing C] [Algebra (A ⧸ I) C]
  [Algebra A C] [IsScalarTower A (A ⧸ I) C]

/-- The henselian lift `W = Spec H_A(C̄)` of `Algebra.ClosedLift`, as an object of the small
pro-étale site of `Spec A` (blueprint `proposition-extension-zero-restriction-closed-subscheme`). -/
noncomputable def closedLiftSpec (A : CommRingCat.{u}) (C : Type u) [CommRing C] [Algebra A C] :
    (Spec A).ProEt :=
  Scheme.ProEt.mk (Spec.map (CommRingCat.ofHom (algebraMap A (Algebra.ClosedLift A C))))

/-- The closed immersion `Spec (A ⧸ I) ⟶ Spec A`. -/
noncomputable abbrev closedSpecι : Spec (.of (A ⧸ I)) ⟶ Spec A :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

variable {I C}

/-- Every nonempty open and closed subscheme of the henselian lift `Spec H_A(C̄)` contains a point
lying over the closed subscheme `Spec (A ⧸ I)`. -/
lemma exists_mem_range_closedSpecι_of_isClopen [Algebra.IndEtale (A ⧸ I) C]
    {s : Set (closedLiftSpec A C).left} (hs : IsClopen s) (hne : s.Nonempty) :
    ∃ x ∈ s, (closedLiftSpec A C).hom.base x ∈ Set.range (closedSpecι I).base := by
  obtain ⟨q, hq⟩ := Algebra.ClosedLift.exists_comap_mem_of_isClopen (A := A) (C := C) hs hne
  refine ⟨_, hq, PrimeSpectrum.comap (algebraMap (A ⧸ I) C) q, ?_⟩
  change PrimeSpectrum.comap (Ideal.Quotient.mk I) (PrimeSpectrum.comap (algebraMap (A ⧸ I) C) q) =
    PrimeSpectrum.comap (algebraMap A (Algebra.ClosedLift A C))
      (PrimeSpectrum.comap (Algebra.ClosedLift.toAlgHom A C : Algebra.ClosedLift A C →+* C) q)
  rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
  congr 1
  ext a
  simp [IsScalarTower.algebraMap_apply A (A ⧸ I) C, Ideal.Quotient.algebraMap_eq]

variable {R : Type (u + 1)} [Ring R] {U : Scheme.{u}} (j : U ⟶ Spec A) [IsOpenImmersion j]

/-- **Extension by zero has no sections over henselian lifts.** If every faithfully flat
ind-étale `C̄`-algebra has a retraction, the extension by zero `j_! N` along an open immersion
`j` missing `Spec (A ⧸ I)` has no nonzero sections over `W = Spec H_A(C̄)`. Every covering of
`W` is refined by a decomposition of `W` into disjoint open and closed pieces; each nonempty
piece meets `Spec (A ⧸ I)`, so it does not map to `U` and the presheaf extension by zero
vanishes on it. -/
theorem subsingleton_openImmersionLowerShriek_closedLiftSpec [Algebra.IndEtale (A ⧸ I) C]
    (hC : ∀ (T : Type u) [CommRing T] [Algebra C T] [Algebra.IndEtale C T]
      [Module.FaithfullyFlat C T], ∃ f : T →+* C, f.comp (algebraMap C T) = RingHom.id C)
    (hj : Disjoint (Set.range j.base) (Set.range (closedSpecι I).base))
    (N : Sheaf (ProEt.topology U) (ModuleCat.{u + 1} R)) :
    Subsingleton (((j)_!open[ModuleCat.{u + 1} R].obj N).obj.obj (op (closedLiftSpec A C))) := by
  set W := closedLiftSpec A C
  let G := MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ (inferInstance : WeaklyEtale j)
  let P := G.op.lan.obj N.obj
  let F : Sheaf (ProEt.topology (Spec A)) (ModuleCat.{u + 1} R) :=
    (presheafToSheaf (ProEt.topology (Spec A)) _).obj P
  change Subsingleton (F.obj.obj (op W))
  have hH := Algebra.ClosedLift.exists_retraction (A := A) (C := C) I hC
  suffices h0 : ∀ x : F.obj.obj (op W), x = 0 from
    ⟨fun x y ↦ by rw [h0 x, h0 y]⟩
  intro x
  obtain ⟨κ, O, hdisj, hcov, hO⟩ :=
    Scheme.ProEt.exists_disjoint_opens_of_forall_exists_retraction
      (R := CommRingCat.of (Algebra.ClosedLift A C)) hH (Iso.refl W.left)
      (Presheaf.imageSieve_mem (ProEt.topology (Spec A))
        (toSheafify (ProEt.topology (Spec A)) P) x)
  have hloc : ∀ k, F.obj.map (Scheme.ProEt.ofOpenImmersionHom W (O k).ι).op x = 0 := by
    intro k
    obtain ⟨t, ht⟩ := hO k
    by_cases hk : (O k : Set W.left).Nonempty
    · -- the presheaf extension by zero vanishes on a piece meeting the closed fibre
      have hclopen : IsClopen (O k : Set W.left) := by
        refine ⟨⟨?_⟩, (O k).isOpen⟩
        have : (O k : Set W.left)ᶜ = ⋃ l ∈ {l | l ≠ k}, (O l : Set W.left) := by
          ext x
          simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
          refine ⟨fun hx ↦ ?_, fun ⟨l, hl, hx⟩ hx' ↦
            (disjoint_iff.1 (hdisj l k hl)).le ⟨hx, hx'⟩⟩
          obtain ⟨l, hl⟩ := hcov x
          exact ⟨l, fun h ↦ hx (h ▸ hl), hl⟩
        rw [this]
        exact isOpen_biUnion fun l _ ↦ (O l).isOpen
      obtain ⟨z, hz, hzZ⟩ := exists_mem_range_closedSpecι_of_isClopen (I := I) hclopen hk
      have : IsEmpty (CostructuredArrow G.op
          (op (Scheme.ProEt.ofOpenImmersion W (O k).ι))) := by
        refine ⟨fun g ↦ ?_⟩
        obtain ⟨y, rfl⟩ : z ∈ Set.range (O k).ι.base := by rw [Opens.range_ι]; exact hz
        have hw := MorphismProperty.Over.w g.hom.unop
        have hy : W.hom.base ((O k).ι.base y) ∈ Set.range j.base := by
          have := congrArg (fun φ ↦ φ.base y) hw
          simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
          refine ⟨(g.left.unop.hom.base (g.hom.unop.left.base y)), ?_⟩
          exact this
        exact (Set.disjoint_iff.1 hj) ⟨hy, hzZ⟩
      have hc := G.op.isPointwiseLeftKanExtensionLeftKanExtensionUnit N.obj
        (op (Scheme.ProEt.ofOpenImmersion W (O k).ι))
      have hz0 : IsZero (P.obj (op (Scheme.ProEt.ofOpenImmersion W (O k).ι))) := by
        rw [IsZero.iff_id_eq_zero]
        exact hc.hom_ext fun g ↦ isEmptyElim g
      rw [← ht, ModuleCat.subsingleton_of_isZero hz0 |>.elim t 0, map_zero]
    · -- sections over the empty scheme vanish
      have : IsEmpty (Scheme.ProEt.ofOpenImmersion W (O k).ι).left := by
        refine ⟨fun y ↦ hk ⟨(O k).ι.base y, ?_⟩⟩
        rw [← Opens.range_ι (O k)]
        exact ⟨y, rfl⟩
      have := Scheme.ProEt.isTerminalSectionsOfIsEmpty F
        (Scheme.ProEt.ofOpenImmersion W (O k).ι)
      exact (ModuleCat.subsingleton_of_isZero this.isZero).elim _ _
  have hS : Sieve.ofArrows _ (fun k ↦ Scheme.ProEt.ofOpenImmersionHom W (O k).ι) ∈
      ProEt.topology (Spec A) W :=
    Scheme.ProEt.mem_topology_of_openImmersion _ (fun k ↦ (O k).ι)
      (fun x ↦ by obtain ⟨k, hk⟩ := hcov x; exact ⟨k, by rw [Opens.range_ι]; exact hk⟩)
      (fun k ↦ Sieve.ofArrows_mk _ _ k)
  have hsh := (isSheaf_iff_isSheaf_of_type _ _).1
    (Presheaf.isSheaf_comp_of_isSheaf _ F.obj (forget (ModuleCat.{u + 1} R)) F.property) _ hS
  rw [← Presieve.isSheafFor_iff_generate] at hsh
  refine hsh.isSeparatedFor.ext fun _ _ ⟨k⟩ ↦ ?_
  change F.obj.map _ x = F.obj.map _ 0
  rw [hloc k, map_zero]

/-- Sections over a weakly contractible object are exact: an epimorphism of sheaves of modules is
surjective on sections over it. -/
lemma surjective_app_of_isWeaklyContractible {T : Scheme.{u}} {W : T.ProEt}
    (hW : (Scheme.ProEt.topology T).IsWeaklyContractible.{u + 1} W)
    {F G : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R)} (φ : F ⟶ G) [Epi φ] :
    Function.Surjective (φ.hom.app (op W)) :=
  hW ((sheafCompose _ (forget _)).map φ)
    ((Presheaf.isLocallySurjective_iff_whisker_forget _ _).1
      ((Sheaf.isLocallySurjective_iff_epi' (φ := φ)).2 inferInstance))

variable [QuasiCompact j]

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme`, part (1): let
`i : Spec (A ⧸ I) ⟶ Spec A` have quasi-compact open complement `j`, and let `C̄` be an ind-étale
`A ⧸ I`-algebra all of whose faithfully flat ind-étale covers split (e.g. a w-contractible one). For
every pro-étale sheaf of modules `F` on `Spec A`, the unit of `i^* ⊣ i_*` gives a bijection
`F(v(V)) ≅ (i^* F)(v(V) ×_X Z)` for the henselian lift `v(V) = Spec H_A(C̄)` of `V = Spec C̄`
(and `v(V) ×_X Z ≅ V` by `Algebra.ClosedLift.bijective_reduction`).

The open–closed sequence `0 ⟶ j_! j^* F ⟶ F ⟶ i_* i^* F ⟶ 0` stays exact on sections over the
weakly contractible `v(V)`, and `j_! j^* F` has no sections there
(`AlgebraicGeometry.ProEtale.subsingleton_openImmersionLowerShriek_closedLiftSpec`). -/
theorem bijective_unit_app_closedLiftSpec [Algebra.IndEtale (A ⧸ I) C]
    (hC : ∀ (T : Type u) [CommRing T] [Algebra C T] [Algebra.IndEtale C T]
      [Module.FaithfullyFlat C T], ∃ f : T →+* C, f.comp (algebraMap C T) = RingHom.id C)
    (hij : IsCompl (Set.range (closedSpecι I).base) (Set.range j.base))
    (F : Sheaf (Scheme.ProEt.topology (Spec A)) (ModuleCat.{u + 1} R)) :
    Function.Bijective
      (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) (closedSpecι I)).unit.app F).hom.app
        (op (closedLiftSpec A C))) := by
  have hS := shortExact_openClosedShortComplex (closedSpecι I) j hij F
  set S := openClosedShortComplex R (closedSpecι I) j hij F
  let E := sheafToPresheaf (Scheme.ProEt.topology (Spec A)) (ModuleCat.{u + 1} R) ⋙
    (CategoryTheory.evaluation _ _).obj (op (closedLiftSpec A C))
  have hH := Algebra.ClosedLift.exists_retraction (A := A) (C := C) I hC
  refine ⟨?_, ?_⟩
  · have hE : (S.map E).Exact := hS.exact.map_of_mono_of_preservesKernel E hS.mono_f
      inferInstance
    have hsub := subsingleton_openImmersionLowerShriek_closedLiftSpec (C := C) j
      hC hij.disjoint.symm ((j)^*[ModuleCat.{u + 1} R].obj F)
    rw [injective_iff_map_eq_zero]
    intro s hs
    obtain ⟨t, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).1 hE s hs
    rw [@Subsingleton.elim _ hsub t 0, map_zero]
  · have := hS.epi_g
    exact surjective_app_of_isWeaklyContractible
      (Scheme.ProEt.isWeaklyContractible_of_forall_exists_retraction
        (R := CommRingCat.of (Algebra.ClosedLift A C)) hH (Iso.refl _)) S.g

end ProEtale

end AlgebraicGeometry
