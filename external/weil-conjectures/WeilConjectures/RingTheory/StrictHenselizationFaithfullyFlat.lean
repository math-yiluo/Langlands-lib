/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.StrictHenselizationTriples
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.RingTheory.ProEtale.FaithfullyFlat
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Faithful flatness of strict henselization

Source: Stacks Project, More on Algebra, Lemma Tag 07QM, part (1), using the
strict henselization of Algebra, Lemma Tag 04GP
(blueprint: lem-sc-strict-henselization-faithfully-flat).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Forget the étale structure morphism, retaining its ring. -/
private noncomputable def flatAffineEtaleRings (R : CommRingCat.{u}) :
    (Spec R).AffineEtaleᵒᵖ ⥤ CommRingCat.{u} where
  obj t := t.unop.left.unop
  map f := f.unop.left.unop

/-- Regard a pointed ring as an arrow from an affine étale ring to `K`. -/
private noncomputable def flatTriplesToPointedRings (R : CommRingCat.{u}) (p : Spec R)
    (K : Type u) [Field K] (χ : (Spec R).residueField p ⟶ CommRingCat.of K) :
    EtaleResidueTriples R p K χ ⥤ CostructuredArrow (flatAffineEtaleRings R) (.of K) where
  obj t := CostructuredArrow.mk (Y := Opposite.op
    (MorphismProperty.CostructuredArrow.mk ⊤ (Spec.map t.α) t.etale))
    ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ)
  map {t s} f := CostructuredArrow.homMk
    (Quiver.Hom.op (MorphismProperty.CostructuredArrow.homMk
      f.hom.right.left.op trivial (by
        have h := congrArg Over.Hom.left (Under.w f.hom)
        simp only [EtaleResidueTriple.factorization, Under.mk_hom, Over.homMk_left,
          Over.comp_left] at h
        change Spec.map f.hom.right.left ≫ Spec.map t.α = Spec.map s.α
        rw [← Spec.map_comp, h]))) (by
      change f.hom.right.left ≫
        ((ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ) =
        (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ
      simpa only [EtaleResidueTriple.factorization,
        Under.mk_right, Over.mk_hom, Category.assoc] using Over.w f.hom.right)
  map_id t := by ext; rfl
  map_comp f g := by ext; rfl

/-- Every map of pointed étale rings comes from a map of triples. -/
private noncomputable def flatTriplesToPointedRingsFullyFaithful
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K) :
    (flatTriplesToPointedRings R p K χ).FullyFaithful where
  preimage {t s} f := InducedCategory.homMk
    (Under.homMk (Over.homMk f.left.unop.left.unop (by
      have h := CostructuredArrow.w f
      change f.left.unop.left.unop ≫
        ((ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ) =
        (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ at h
      simpa only [EtaleResidueTriple.factorization, Under.mk_right, Over.mk_hom,
        Category.assoc] using h)) (by
      apply Over.OverMorphism.ext
      change t.α ≫ f.left.unop.left.unop = s.α
      apply Spec.map_injective
      rw [Spec.map_comp]
      exact f.left.unop.w))
  map_preimage f := by ext; rfl
  preimage_map f := by ext; rfl

/-- The canonical map from a local ring to the colimit of its etale residue triples,
pointed in a separable closure of its residue field, is faithfully flat.
Source: Stacks Project, More on Algebra, Tag 07QM (1), and Algebra, Tag 04GP.
(blueprint: lem-sc-strict-henselization-faithfully-flat).

Proof:
1. Apply lem-weil-pbc-strict-henselization-triples at the maximal ideal. Its colimit
is the strict henselization, and the compatibility of the structure maps identifies
`ρ` with the canonical map from `R` to this colimit. The chosen residue embedding
is the one specified by the algebra structure on `K`.
2. Each ring in the diagram is etale over `R`, hence flat by
lem-weil-pbc-etale-algebra-flat. The underlying module of the ring colimit is the
filtered colimit of these flat modules, so lem-weil-pbc-filtered-colimit-flat-modules
makes the colimit flat over `R`.
3. By lem-weil-pbc-strict-henselization-triples the colimit is local, and its maximal
ideal contracts to the maximal ideal of `R`. Thus `ρ` is a local ring map. A flat
local homomorphism of local rings is faithfully flat, by
lem-pc-local-flat-faithful-flat-reflects-surjective. -/
theorem strictHenselization_faithfullyFlat
    (R : CommRingCat.{u}) [IsLocalRing R] (p : Spec R)
    (hp : p.asIdeal = IsLocalRing.maximalIdeal R)
    (K : Type u) [Field K] [Algebra ((Spec R).residueField p) K]
    [IsSepClosure ((Spec R).residueField p) K]
    (c : Cocone (etaleResidueTriplesRingDiagram R p K
      (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K))))
    (hc : IsColimit c) (ρ : R ⟶ c.pt)
    (hρ : ∀ t : EtaleResidueTriples R p K
      (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K)),
      t.α ≫ c.ι.app t = ρ) :
    ρ.hom.FaithfullyFlat := by
  classical
  let χ := CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K)
  let D := etaleResidueTriplesRingDiagram R p K χ
  obtain ⟨hfiltered, c₀, ⟨hc₀⟩, hlocal, ρ₀, ψ₀, hρ₀, _, _, hm₀, _, hcontract, _⟩ :=
    strictHenselization_triples R p K
  have := hfiltered
  have := hlocal
  have : IsLocalHom ρ₀.hom := by
    apply ((IsLocalRing.local_hom_TFAE ρ₀.hom).out 5 1).mp
    rw [hm₀, hcontract, hp]
  let e := hc.coconePointUniqueUpToIso hc₀
  have he : ρ ≫ e.hom = ρ₀ := by
    let t₀ : EtaleResidueTriples R p K χ :=
      ⟨R, 𝟙 R, inferInstance, p, by simp, χ, by simp⟩
    have h₁ : c.ι.app t₀ = ρ := by simpa [t₀] using hρ t₀
    have h₂ : c₀.ι.app t₀ = ρ₀ := by simpa [t₀] using hρ₀ t₀
    rw [← h₁, hc.comp_coconePointUniqueUpToIso_hom hc₀, h₂]
  have : IsLocalRing c.pt := e.symm.commRingCatIsoToRingEquiv.isLocalRing
  have : IsLocalHom (e.hom.hom.comp ρ.hom) := by
    change IsLocalHom (ρ ≫ e.hom).hom
    rw [he]
    infer_instance
  have : IsLocalHom ρ.hom := isLocalHom_of_comp ρ.hom e.hom.hom
  have : (flatTriplesToPointedRings R p K χ).Full :=
    (flatTriplesToPointedRingsFullyFaithful R p K χ).full
  have : (flatTriplesToPointedRings R p K χ).Faithful :=
    (flatTriplesToPointedRingsFullyFaithful R p K χ).faithful
  have : EssentiallySmall.{u} (EtaleResidueTriples R p K χ) :=
    essentiallySmall_of_fully_faithful (flatTriplesToPointedRings R p K χ)
  let E := (equivSmallModel.{u} (EtaleResidueTriples R p K χ)).symm
  have : IsFiltered (SmallModel.{u} (EtaleResidueTriples R p K χ)) :=
    IsFiltered.of_equivalence E.symm
  let t : (Functor.const (SmallModel.{u} (EtaleResidueTriples R p K χ))).obj R ⟶
      E.functor ⋙ D :=
    { app := fun i ↦ (E.functor.obj i).α
      naturality := fun i j f ↦ by
        dsimp only [Functor.const_obj_map, Functor.const_obj_obj]
        rw [Category.id_comp]
        have h := congrArg Over.Hom.left (Under.w (E.functor.map f).hom)
        change (E.functor.obj j).α =
          (E.functor.obj i).α ≫ (E.functor.map f).hom.right.left
        simpa only [EtaleResidueTriple.factorization, Under.mk_hom, Over.homMk_left,
          Over.comp_left] using h.symm }
  have hflat : ρ.hom.Flat := by
    apply RingHom.Flat.of_isColimit ρ
      (SmallModel.{u} (EtaleResidueTriples R p K χ)) (E.functor ⋙ D)
      (t := t) (c := (c.whisker E.functor).ι) (hc.whiskerEquivalence E)
    intro i
    refine ⟨?_, hρ (E.functor.obj i)⟩
    have := (E.functor.obj i).etale
    have hEtale : (E.functor.obj i).α.hom.Etale :=
      (HasRingHomProperty.Spec_iff (P := @Etale)).mp inferInstance
    let := (E.functor.obj i).α.hom.toAlgebra
    have := hEtale.toAlgebra
    exact RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat R (E.functor.obj i).B)
  let := ρ.hom.toAlgebra
  have : Module.Flat R c.pt := hflat
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

end AlgebraicGeometry.Scheme
