/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.PointFunctions
public import WeilConjectures.AlgebraicGeometry.ZeroDimensionalCohomology
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.DisjointUnion

/-!
# The direct image along a geometric point is exact

Let `k` be a separably closed field. An étale scheme `V` over `Spec k` is a disjoint union of
points with residue field `k`, so that the sections of an étale sheaf over `V` are a product of
its global sections. Hence an epimorphism of étale sheaves of `Λ`-modules on `Spec k` is
surjective on sections over every étale `Spec k`-scheme
(`AlgebraicGeometry.Scheme.surjective_app_of_epi_of_isSepClosed'`), and the direct image
`x_*` along a geometric point `x : Spec k ⟶ X` is exact
(`AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isSepClosed`): it is computed
by sections over the étale `Spec k`-schemes `U ×_X Spec k`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Scheme

/-- The residue fields of a scheme étale over a scheme with separably closed residue fields are
separably closed. -/
lemma isSepClosed_residueField_of_etale {S V : Scheme.{u}} (p : V ⟶ S) [Etale p] (v : V)
    [IsSepClosed (S.residueField (p v))] : IsSepClosed (V.residueField v) := by
  have := p.etale_residueFieldMap v
  algebraize [(p.residueFieldMap v).hom]
  have hs := IsSepClosed.algebraMap_surjective (S.residueField (p v)) (V.residueField v)
  exact IsSepClosed.of_ringEquiv
    (RingEquiv.ofBijective _ ⟨(algebraMap (S.residueField (p v)) _).injective, hs⟩)

variable {k : Type u} [Field k] [IsSepClosed k]

/-- The residue field of `Spec k` is separably closed. -/
instance isSepClosed_residueField_spec (x : Spec (.of k)) :
    IsSepClosed ((Spec (.of k)).residueField x) :=
  IsSepClosed.of_ringEquiv ((Ideal.algEquivResidueFieldOfField x.asIdeal).toRingEquiv.trans
    (Spec.residueFieldIso (.of k) x).commRingCatIsoToRingEquiv.symm)

/-- Let `W` be an étale scheme with a single point over a scheme `S`, with separably closed
residue field. Every covering sieve of `W` in the small étale site of `S` contains the identity:
an étale `S`-scheme over `W` hitting its point has a section. -/
lemma id_mem_of_mem_smallEtaleTopology_of_subsingleton {S : Scheme.{u}} {W : S.Etale}
    [Subsingleton W.left] (hsep : ∀ w : W.left, IsSepClosed (W.left.residueField w))
    {R : Sieve W} (hR : R ∈ S.smallEtaleTopology W) (w : W.left) : R.arrows (𝟙 W) := by
  obtain ⟨W', g, w', hg, -⟩ := exists_of_mem_smallEtaleTopology hR w
  obtain ⟨σ, hσ, -⟩ := exists_section_of_etale_of_subsingleton hsep g.left
    (W'.left.fromSpecResidueField w')
  let σ' : W ⟶ W' := MorphismProperty.Over.homMk σ (by
    rw [← MorphismProperty.Over.w g, ← Category.assoc, hσ, Category.id_comp])
  have h : σ' ≫ g = 𝟙 W := MorphismProperty.Over.Hom.ext hσ
  rw [← h]
  exact R.downward_closed hg σ'

variable (Λ : Type (u + 1)) [Ring Λ]

/-- Over a separably closed field `k`, an epimorphism of étale sheaves of `Λ`-modules on
`Spec k` is surjective on sections over every étale `Spec k`-scheme `V`: `V` is the disjoint
union of its points, over each of which the sections lift, and the lifts glue. -/
lemma surjective_app_of_epi_of_isSepClosed'
    {F G : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)} (p : F ⟶ G) [Epi p]
    (V : (Spec (.of k)).Etaleᵒᵖ) : Function.Surjective (p.hom.app V) := by
  intro s
  have : Unique (Spec (.of k)) := inferInstanceAs (Unique (PrimeSpectrum k))
  have := (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{u + 1} Λ) p).2 inferInstance
  have hR := Presheaf.imageSieve_mem (Spec (.of k)).smallEtaleTopology p.hom s
  have := discreteTopology_of_etale_of_unique V.unop
  have : Etale V.unop.hom := V.unop.prop
  let U (v : V.unop.left) : V.unop.left.Opens := ⟨{v}, isOpen_discrete _⟩
  let W (v : V.unop.left) : (Spec (.of k)).Etale := Etale.mk ((U v).ι ≫ V.unop.hom)
  let i (v : V.unop.left) : W v ⟶ V.unop := MorphismProperty.Over.homMk (U v).ι rfl
  have : ∀ v, IsOpenImmersion (i v).left := fun v ↦ inferInstanceAs (IsOpenImmersion (U v).ι)
  have hlift (v : V.unop.left) : ∃ t, p.hom.app (op (W v)) t = G.obj.map (i v).op s := by
    have : Subsingleton (W v).left := (Set.subsingleton_singleton (a := v)).coe_sort
    have hsep (w : (W v).left) : IsSepClosed ((W v).left.residueField w) :=
      isSepClosed_residueField_of_etale (S := Spec (.of k)) (W v).hom w
    have hmem := id_mem_of_mem_smallEtaleTopology_of_subsingleton hsep
      ((Spec (.of k)).smallEtaleTopology.pullback_stable (i v) hR) ⟨v, Set.mem_singleton v⟩
    obtain ⟨t, ht⟩ := hmem
    exact ⟨t, by simpa using ht⟩
  choose t ht using hlift
  have hdisj : Pairwise fun v w ↦
      Disjoint (Set.range (i v).left.base) (Set.range (i w).left.base) := fun v w hvw ↦ by
    change Disjoint (Set.range (U v).ι) (Set.range (U w).ι)
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    simpa [U] using hvw
  have hcov : ⋃ v, Set.range (i v).left.base = Set.univ := by
    refine Set.eq_univ_of_forall fun v ↦ Set.mem_iUnion.2 ⟨v, ?_⟩
    change v ∈ Set.range (U v).ι
    rw [Scheme.Opens.range_ι]
    rfl
  let e {M : ModuleCat.{u + 1} Λ} (m : M) : ModuleCat.of Λ Λ ⟶ M :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton Λ M m)
  obtain ⟨σ, hσ, -⟩ := Etale.existsUnique_of_pairwise_disjoint F W i hdisj hcov
    (fun v ↦ e (t v))
  refine ⟨σ.hom 1, ?_⟩
  have huniq := Etale.existsUnique_of_pairwise_disjoint G W i hdisj hcov
    (fun v ↦ e (G.obj.map (i v).op s))
  have h₁ : σ ≫ p.hom.app (op V.unop) = e s :=
    huniq.unique (y₁ := σ ≫ p.hom.app (op V.unop)) (y₂ := e s)
      (fun v ↦ by
        rw [Category.assoc, ← p.hom.naturality, reassoc_of% (hσ v)]
        ext
        simp [e, ht])
      (fun v ↦ by
        ext
        simp [e])
  have h₂ := congrArg (fun f ↦ f.hom 1) h₁
  simpa [e] using h₂

end Scheme

namespace Etale

variable {k : Type u} [Field k] [IsSepClosed k] (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
  (x : Spec (.of k) ⟶ X)

/-- The direct image along a geometric point `x : Spec k ⟶ X` preserves epimorphisms of étale
sheaves of `Λ`-modules: it is computed by sections over étale `Spec k`-schemes, over which
epimorphisms are surjective. -/
instance preservesEpimorphisms_lowerStar_of_isSepClosed :
    ((x)_*[ModuleCat.{u + 1} Λ]).PreservesEpimorphisms where
  preserves p _ := epi_lowerStar_map_of_surjective x p
    (fun _ ↦ Scheme.surjective_app_of_epi_of_isSepClosed' Λ p _)

/-- The direct image along a geometric point `x : Spec k ⟶ X` is exact. -/
instance preservesFiniteColimits_lowerStar_of_isSepClosed :
    PreservesFiniteColimits ((x)_*[ModuleCat.{u + 1} Λ]) := by
  have h := (Functor.preservesFiniteLimits_tfae ((x)_*[ModuleCat.{u + 1} Λ])).out 4 1
  have h' := (Functor.preservesFiniteColimits_tfae ((x)_*[ModuleCat.{u + 1} Λ])).out 1 4
  exact h'.1 fun S hS ↦ ⟨(h.1 inferInstance S hS).1, by have := hS.epi_g; infer_instance⟩

end Etale

end AlgebraicGeometry
