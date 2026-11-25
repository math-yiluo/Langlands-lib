/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsStrictHenselization
public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples

import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Filtered.Connected
import WeilConjectures.RingTheory.EtaleResidueTriplesFiltered

/-!
# Comparing two colimit presentations of strict henselization

Source: Stacks Project, Algebra, Tag 04GW, the pointed-algebra description of triples.
(blueprint: lem-sc-strict-henselization-triples-presentation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace Algebra

set_option backward.isDefEq.respectTransparency.types false in
private lemma closedPoint_residue_structure
    (R K : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K] [IsSepClosure (IsLocalRing.ResidueField R) K]
    [Algebra R K] [IsScalarTower R (IsLocalRing.ResidueField R) K] :
    ∃ (a : Algebra ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) K),
      let := a
      IsSepClosure ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) K ∧
      (ΓSpecIso (CommRingCat.of R)).inv ≫
        (Spec (CommRingCat.of R)).Γevaluation (IsLocalRing.closedPoint R) ≫
        CommRingCat.ofHom (algebraMap
          ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) K) =
        CommRingCat.ofHom (algebraMap R K) := by
  let p : Spec (CommRingCat.of R) := IsLocalRing.closedPoint R
  let e₀ : IsLocalRing.ResidueField R ≃+* p.asIdeal.ResidueField :=
    RingEquiv.ofBijective _
      (IsLocalRing.maximalIdeal R).bijective_algebraMap_quotient_residueField
  let e : (Spec (CommRingCat.of R)).residueField p ≃+* IsLocalRing.ResidueField R :=
    (Spec.residueFieldIso (CommRingCat.of R) p).commRingCatIsoToRingEquiv.trans e₀.symm
  let a := ((algebraMap (IsLocalRing.ResidueField R) K).comp e.toRingHom).toAlgebra
  let := a
  refine ⟨a, ?_, ?_⟩
  · exact ⟨IsSepClosure.sep_closed (IsLocalRing.ResidueField R),
      Algebra.IsSeparable.of_equiv_equiv e.symm (RingEquiv.refl K) (by
        ext x
        simp [a, RingHom.algebraMap_toAlgebra])⟩
  · have h : CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField) ≫
        CommRingCat.ofHom e₀.symm.toRingHom =
        CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)) := by
      ext r
      change e₀.symm (algebraMap R p.asIdeal.ResidueField r) = _
      change e₀.symm (e₀ (IsLocalRing.residue R r)) = _
      exact e₀.symm_apply_apply _
    change (ΓSpecIso (CommRingCat.of R)).inv ≫
      (Spec (CommRingCat.of R)).Γevaluation p ≫
      (Spec.residueFieldIso (CommRingCat.of R) p).hom ≫
      CommRingCat.ofHom e₀.symm.toRingHom ≫
      CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField R) K) = _
    have hspec := Spec.algebraMap_residueFieldIso_inv (CommRingCat.of R) p
    change CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField) ≫
      (Spec.residueFieldIso (CommRingCat.of R) p).inv =
      (ΓSpecIso (CommRingCat.of R)).inv ≫
        (Spec (CommRingCat.of R)).Γevaluation p at hspec
    have hspec' : (ΓSpecIso (CommRingCat.of R)).inv ≫
        (Spec (CommRingCat.of R)).Γevaluation p ≫
        (Spec.residueFieldIso (CommRingCat.of R) p).hom =
        CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField) := by
      have heq := congrArg
        (fun f ↦ f ≫ (Spec.residueFieldIso (CommRingCat.of R) p).hom) hspec
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using heq.symm
    simp only [← Category.assoc] at hspec' ⊢
    rw [hspec', h]
    ext r
    exact (IsScalarTower.algebraMap_apply R (IsLocalRing.ResidueField R) K r).symm

private abbrev PointedEtale (R K : Type u) [CommRing R] [Field K] [Algebra R K] :=
  ObjectProperty.FullSubcategory (fun X : Over (CommAlgCat.of R K) ↦ Etale R X.left)

private noncomputable def triplePointedObj
    (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    (p : Spec (CommRingCat.of R))
    (χ : (Spec (CommRingCat.of R)).residueField p ⟶ CommRingCat.of K)
    (hχ : (ΓSpecIso (CommRingCat.of R)).inv ≫
      (Spec (CommRingCat.of R)).Γevaluation p ≫ χ =
      CommRingCat.ofHom (algebraMap R K))
    (t : EtaleResidueTriples (CommRingCat.of R) p K χ) : PointedEtale R K := by
  letI := t.α.hom.toAlgebra
  let b := (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ
  let f : t.B →ₐ[R] K :=
    { b.hom with
      commutes' := fun r ↦ by
        have h := t.compatible.trans hχ
        exact congrArg (fun g : CommRingCat.of R ⟶ CommRingCat.of K ↦ g.hom r) h }
  refine ⟨Over.mk (CommAlgCat.ofHom f), ?_⟩
  change Algebra.Etale R t.B
  rw [← RingHom.etale_algebraMap]
  exact (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)).mp t.etale

private noncomputable def triplesPointedFunctor
    (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    (p : Spec (CommRingCat.of R))
    (χ : (Spec (CommRingCat.of R)).residueField p ⟶ CommRingCat.of K)
    (hχ : (ΓSpecIso (CommRingCat.of R)).inv ≫
      (Spec (CommRingCat.of R)).Γevaluation p ≫ χ =
      CommRingCat.ofHom (algebraMap R K)) :
    EtaleResidueTriples (CommRingCat.of R) p K χ ⥤ PointedEtale R K where
  obj := triplePointedObj R K p χ hχ
  map {s t} f := by
    letI := s.α.hom.toAlgebra
    letI := t.α.hom.toAlgebra
    exact ObjectProperty.homMk (Over.homMk
      (CommAlgCat.ofHom
        { f.hom.right.left.hom with
          commutes' := fun r ↦ by
            have h := congrArg CommaMorphism.left (Under.w f.hom)
            exact congrArg (fun g : CommRingCat.of R ⟶ t.B ↦ g.hom r) h }) (by
        apply CommAlgCat.hom_ext
        ext r
        exact congrArg (fun g : s.B ⟶ CommRingCat.of K ↦ g.hom r) (Over.w f.hom.right)))
  map_id t := by rfl
  map_comp f g := by rfl

private noncomputable def triplesPointedFullyFaithful
    (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    (p : Spec (CommRingCat.of R))
    (χ : (Spec (CommRingCat.of R)).residueField p ⟶ CommRingCat.of K)
    (hχ : (ΓSpecIso (CommRingCat.of R)).inv ≫
      (Spec (CommRingCat.of R)).Γevaluation p ≫ χ =
      CommRingCat.ofHom (algebraMap R K)) :
    (triplesPointedFunctor R K p χ hχ).FullyFaithful where
  preimage {s t} f := InducedCategory.homMk (Under.homMk
    (Over.homMk (CommRingCat.ofHom f.hom.left.hom.toRingHom) (by
      exact congrArg (fun g ↦ CommRingCat.ofHom g.hom.toRingHom) (Over.w f.hom))) (by
        apply Over.OverMorphism.ext
        ext r
        exact f.hom.left.hom.commutes r))
  map_preimage f := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    rfl
  preimage_map f := by
    apply InducedCategory.hom_ext
    apply Under.UnderMorphism.ext
    apply Over.OverMorphism.ext
    rfl

private lemma exists_pointing (B : CommRingCat.{u}) (K : Type u) [Field K]
    (b : B ⟶ CommRingCat.of K) :
    ∃ (q : Spec B) (φ : (Spec B).residueField q ⟶ CommRingCat.of K),
      (ΓSpecIso B).inv ≫ (Spec B).Γevaluation q ≫ φ = b := by
  have hpoint (q : Spec B) (φ : (Spec B).residueField q ⟶ CommRingCat.of K) :
      Spec.map ((ΓSpecIso B).inv ≫ (Spec B).Γevaluation q ≫ φ) =
        Spec.map φ ≫ (Spec B).fromSpecResidueField q := by
    simp only [fromSpecResidueField, Spec.fromSpecStalk_eq, ← Spec.map_comp]
    rfl
  generalize he : (SpecToEquivOfField K (Spec B)) (Spec.map b) = z
  obtain ⟨q, φ⟩ := z
  refine ⟨q, φ, ?_⟩
  apply Spec.map_injective
  rw [hpoint]
  have h := (SpecToEquivOfField K (Spec B)).symm_apply_apply (Spec.map b)
  rw [he] at h
  exact h

private lemma pointing_over (R B : CommRingCat.{u}) (p : Spec R)
    (K : Type u) [Field K] (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (a : R ⟶ B) (q : Spec B) (φ : (Spec B).residueField q ⟶ CommRingCat.of K)
    (hc : a ≫ (ΓSpecIso B).inv ≫ (Spec B).Γevaluation q ≫ φ =
      (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ) :
    Spec.map a q = p := by
  have hpoint (B : CommRingCat.{u}) (q : Spec B)
      (φ : (Spec B).residueField q ⟶ CommRingCat.of K) :
      Spec.map ((ΓSpecIso B).inv ≫ (Spec B).Γevaluation q ≫ φ) =
        Spec.map φ ≫ (Spec B).fromSpecResidueField q := by
    simp only [fromSpecResidueField, Spec.fromSpecStalk_eq, ← Spec.map_comp]
    rfl
  have h := congrArg Spec.map hc
  rw [Spec.map_comp, hpoint, hpoint] at h
  have h' := congrArg
    (fun f : Spec (CommRingCat.of K) ⟶ Spec R ↦ f (IsLocalRing.closedPoint K)) h
  simpa using h'

private lemma triplesPointedEssSurj
    (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    (p : Spec (CommRingCat.of R))
    (χ : (Spec (CommRingCat.of R)).residueField p ⟶ CommRingCat.of K)
    (hχ : (ΓSpecIso (CommRingCat.of R)).inv ≫
      (Spec (CommRingCat.of R)).Γevaluation p ≫ χ =
      CommRingCat.ofHom (algebraMap R K)) :
    (triplesPointedFunctor R K p χ hχ).EssSurj := by
  refine ⟨fun X ↦ ?_⟩
  let B := CommRingCat.of X.obj.left
  let a : CommRingCat.of R ⟶ B := CommRingCat.ofHom (algebraMap R X.obj.left)
  let b : B ⟶ CommRingCat.of K := CommRingCat.ofHom X.obj.hom.hom.toRingHom
  obtain ⟨q, φ, hφ⟩ := exists_pointing B K b
  have hc : a ≫ (ΓSpecIso B).inv ≫ (Spec B).Γevaluation q ≫ φ =
      (ΓSpecIso (CommRingCat.of R)).inv ≫ (Spec (CommRingCat.of R)).Γevaluation p ≫ χ := by
    rw [hφ, hχ]
    ext r
    exact X.obj.hom.hom.commutes r
  let t : EtaleResidueTriples (CommRingCat.of R) p K χ :=
    { B := B
      α := a
      etale := (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)).mpr
        (RingHom.etale_algebraMap.mpr X.property)
      q := q
      over := pointing_over _ B p K χ a q φ hc
      φ := φ
      compatible := hc }
  let A := (triplePointedObj R K p χ hχ t).obj.left
  refine ⟨t, ⟨ObjectProperty.isoMk _ (Over.isoMk
    (@CommAlgCat.isoMk R _ A X.obj.left A.commRing X.obj.left.commRing
      A.algebra X.obj.left.algebra
    { toEquiv := Equiv.refl _
      map_mul' := fun x y ↦ rfl
      map_add' := fun x y ↦ rfl
      commutes' := fun r ↦ rfl }) ?_)⟩⟩
  apply CommAlgCat.hom_ext
  ext x
  exact (congrArg (fun g : B ⟶ CommRingCat.of K ↦ g.hom x) hφ).symm

/-- Residue triples identify the diagram of pointed etale algebras, including its base maps.
Source: Stacks Project, Algebra, Tag 04GW, proof of Lemma 10.155.11.

Proof: Equip the ring B of a triple with the R-algebra structure given by its map alpha.
The pointing B to K is evaluation followed by the residue embedding. The hypothesis hchi
and the triple compatibility say it is an R-algebra map. The affine criterion for etaleness
identifies the scheme and algebra etale conditions. Send a morphism to the same ring map;
the equations in the induced under-over category say precisely that it commutes with R
and K. This identifies each hom set. Conversely an etale R-algebra pointed in K gives a
morphism Spec K to Spec B. The field-point/residue-field correspondence supplies its
prime q and residue embedding. Compatibility on R forces q to lie above p, so it is a
triple. This yields essential surjectivity and hence an equivalence. The underlying ring
is unchanged in this construction; identity maps give the natural diagram isomorphism,
and its compatibility with alpha is the definition of the induced R-algebra structure.
The argument applies to arbitrary p and arbitrary field K; it uses no closure property.
(blueprint: lem-sc-strict-henselization-triples-presentation). -/
private theorem etaleResidueTriples_pointed_comparison
    (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    (p : Spec (CommRingCat.of R))
    (χ : (Spec (CommRingCat.of R)).residueField p ⟶ CommRingCat.of K)
    (hχ : (ΓSpecIso (CommRingCat.of R)).inv ≫
      (Spec (CommRingCat.of R)).Γevaluation p ≫ χ =
      CommRingCat.ofHom (algebraMap R K)) :
    let P : ObjectProperty (Over (CommAlgCat.of R K)) := fun X ↦ Etale R X.left
    ∃ (e : EtaleResidueTriples (CommRingCat.of R) p K χ ≌ P.FullSubcategory)
      (d : e.functor ⋙ P.ι ⋙ Over.forget (CommAlgCat.of R K) ⋙
        forget₂ (CommAlgCat R) CommRingCat ≅
        etaleResidueTriplesRingDiagram (CommRingCat.of R) p K χ),
      ∀ t, CommRingCat.ofHom (algebraMap R (e.functor.obj t).obj.left) ≫
        d.hom.app t = t.α := by
  let P : ObjectProperty (Over (CommAlgCat.of R K)) := fun X ↦ Etale R X.left
  let F := triplesPointedFunctor R K p χ hχ
  let := (triplesPointedFullyFaithful R K p χ hχ).full
  let := (triplesPointedFullyFaithful R K p χ hχ).faithful
  let := triplesPointedEssSurj R K p χ hχ
  let : F.IsEquivalence := {}
  let d : F ⋙ P.ι ⋙ Over.forget (CommAlgCat.of R K) ⋙
      forget₂ (CommAlgCat R) CommRingCat ≅
      etaleResidueTriplesRingDiagram (CommRingCat.of R) p K χ :=
    NatIso.ofComponents (fun t ↦ Iso.refl t.B) (by
      intro s t f
      change f.hom.right.left ≫ 𝟙 t.B = 𝟙 s.B ≫ f.hom.right.left
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  refine ⟨F.asEquivalence, d, ?_⟩
  intro t
  change t.α ≫ 𝟙 t.B = t.α
  exact Category.comp_id _


/-- A strict henselization specified using pointed etale algebras is also a colimit
of residue triples, with exactly the original structural map from the base ring.
Source: Stacks Project, Tag 04GW, the identification of triples with pointed algebras.

Proof: Take the point `p` corresponding to the maximal ideal of `R`. Its scheme
residue field is canonically isomorphic over `R` to `R/m`. Transport the given algebra
structure and separable-closure structure on `K` along this isomorphism.
Send a residue triple to its etale `R`-algebra `B` with map to `K` given by evaluation
at its prime followed by its residue embedding. The compatibility equation makes
this an `R`-algebra map. Morphisms are precisely the algebra maps commuting with
these maps to `K`, so this functor is fully faithful. Conversely, for a pointed
etale algebra `B → K`, use `SpecToEquivOfField` on the induced morphism `Spec K → Spec B`
to obtain its prime and residue embedding. Apply `Spec.map` to the compatibility
equation and evaluate at the unique point of `Spec K` to show the prime lies over `p`.
The identity on `B` gives an isomorphism back to the pointed algebra. Thus the functor
is an equivalence, identifying the ring diagrams and their structural maps from `R`.
Transport the universal cocone in `hC` along this equivalence and the given
isomorphism of its vertex with `C`. Forgetting the algebra structure preserves
this colimit: the triples category is filtered, hence nonempty and connected;
a ring cocone acquires a unique compatible `R`-algebra structure from the common
maps out of `R`. Thus the transported cocone is a ring colimit with vertex `C`.
Every leg is an `R`-algebra map, giving the final displayed compatibility.
(blueprint: lem-sc-strict-henselization-triples-presentation). -/
theorem IsStrictHenselization.triples_presentation
    (R K C : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K] [IsSepClosure (IsLocalRing.ResidueField R) K]
    [Algebra R K] [IsScalarTower R (IsLocalRing.ResidueField R) K]
    [CommRing C] [Algebra R C] (hC : IsStrictHenselization R K C) :
    ∃ (p : Spec (CommRingCat.of R)), p.asIdeal = IsLocalRing.maximalIdeal R ∧
      ∃ (a : Algebra ((Spec (CommRingCat.of R)).residueField p) K),
        letI := a
        IsSepClosure ((Spec (CommRingCat.of R)).residueField p) K ∧
        ∃ (ι : etaleResidueTriplesRingDiagram (CommRingCat.of R) p K
            (CommRingCat.ofHom (algebraMap ((Spec (CommRingCat.of R)).residueField p) K)) ⟶
            (Functor.const _).obj (CommRingCat.of C)),
          Nonempty (IsColimit (Cocone.mk (CommRingCat.of C) ι)) ∧
          ∀ t, t.α ≫ ι.app t = CommRingCat.ofHom (algebraMap R C) := by
  classical
  let p : Spec (CommRingCat.of R) := IsLocalRing.closedPoint R
  obtain ⟨a, hs, hχ⟩ := closedPoint_residue_structure R K
  let := a
  let χ := CommRingCat.ofHom (algebraMap ((Spec (CommRingCat.of R)).residueField p) K)
  let P : ObjectProperty (Over (CommAlgCat.of R K)) := fun X ↦ Etale R X.left
  let D := P.ι ⋙ Over.forget (CommAlgCat.of R K)
  obtain ⟨e, d, hd⟩ := etaleResidueTriples_pointed_comparison R K p χ hχ
  obtain ⟨c, ⟨hc⟩, ⟨i⟩⟩ := hC
  let cC : Cocone D := c.extend i.hom
  have hcC : IsColimit cC := hc.ofIsoColimit (c.extendIso i)
  let cT := cC.whisker e.functor
  have hcT : IsColimit cT := hcC.whiskerEquivalence e
  let F := forget₂ (CommAlgCat R) CommRingCat
  let : IsFiltered (EtaleResidueTriples (CommRingCat.of R) p K χ) :=
    etaleResidueTriples_filtered_part (CommRingCat.of R) p K χ
  let : IsConnected (EtaleResidueTriples (CommRingCat.of R) p K χ) :=
    IsFiltered.isConnected _
  have : PreservesColimitsOfShape (EtaleResidueTriples (CommRingCat.of R) p K χ) F := by
    change PreservesColimitsOfShape _
      ((commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙ Under.forget _)
    infer_instance
  let cR := F.mapCocone cT
  have hcR : IsColimit cR := isColimitOfPreserves F hcT
  let c' := (Cocone.precompose d.inv).obj cR
  have hc' : IsColimit c' := (IsColimit.precomposeHomEquiv d.symm cR).symm hcR
  refine ⟨p, rfl, a, hs, c'.ι, ⟨hc'⟩, ?_⟩
  intro t
  change t.α ≫ d.inv.app t ≫ F.map (cC.ι.app (e.functor.obj t)) = _
  rw [← hd t, Category.assoc, d.hom_inv_id_app_assoc]
  ext r
  exact (cC.ι.app (e.functor.obj t)).hom.commutes r

end Algebra
