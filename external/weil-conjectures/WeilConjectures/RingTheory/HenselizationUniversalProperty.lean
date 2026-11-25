/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PairHenselization
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.RingTheory.HenselizationStageMap

/-!
# Universal property of the henselization of a pair

Source: Stacks Project, More on Algebra, Tag 0A02, last paragraph of the proof
(blueprint: lem-weil-pbc-henselization-universal-property).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

/-- The henselization of a pair has the universal property of a henselian pair.
Source: Stacks Project, More on Algebra, Tag 0A02
(blueprint: lem-weil-pbc-henselization-universal-property).

The colimit cocone `c` represents `(Bʰ, Jʰ)`, and `c.pt.hom.hom` is its structural
map `η : B → Bʰ`; the ideal in the colimit is `J.map c.pt.hom.hom`. For a henselian
pair `(A', I')` and a map `φ` carrying `J` into `I'`, the displayed existential gives
the unique factorization and records that the factorization carries `Jʰ` into `I'`.

Proof: use the sections of `A' ⊗[B] C` supplied by the Gabber root criterion for each
étale stage, prove their uniqueness by the idempotent splitting of the diagonal and
idempotents modulo the Jacobson radical, and pass to the colimit. The colimit
universal property gives existence and uniqueness; `Jʰ = JBʰ` gives the ideal inclusion.

Proof steps from the blueprint: (1) use the identity object and the colimit cocone to
identify the structural map with the coprojection of `B`; (2) obtain the
Jacobson-radical and root-lifting conditions from `HenselianRing` via
`lem-weil-pbc-henselian-factorization-criterion`; (3) for each stage form
`A' ⊗[B] C`, which is étale over `A'` and reduces to `A'/I'`; (4) lift the
reduced section using `lem-weil-pbc-gabber-root-criterion-etale-section-lifting`;
(5) prove uniqueness of each section by the étale diagonal idempotent splitting
and `lem-weil-pbc-idempotents-determined-modulo-radical`; (6) check compatibility
and use the colimit to construct `ψ`; (7) compare any other factorization
stagewise and use the ring-colimit universal property for uniqueness; (8) since
`Jʰ = J Bʰ`, the image of `Jʰ` under `ψ` lies in `I'` by `hφ` and ideal closure.
These steps use `lem-weil-pbc-pair-henselization`, `def-weil-pbc-category-colimit`,
`lem-weil-pbc-filtered-colimit-algebras-elementwise`,
`definition-torsion-sheaves--3`,
`lem-weil-pbc-etale-ring-base-change`, and
`lem-weil-pbc-etale-section-idempotent-splitting` as cited by the node.
-/
theorem henselization_universal_property (B : Type u) [CommRing B] (J : Ideal B)
    (c : Cocone (ObjectProperty.ι (fun C : Under (CommRingCat.of B) ↦
      AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
        Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
          (Ideal.le_comap_map)))))
    (hc : Nonempty (IsColimit c))
    (A' : Type u) [CommRing A'] (I' : Ideal A') [HenselianRing A' I']
    (φ : B →+* A') (hφ : J.map φ ≤ I') :
    ∃ ψ : c.pt.right →+* A',
      RingHom.comp ψ (CommRingCat.Hom.hom c.pt.hom) = φ ∧
        (J.map (CommRingCat.Hom.hom c.pt.hom)).map ψ ≤ I' ∧
        ∀ ψ' : c.pt.right →+* A', RingHom.comp ψ' (CommRingCat.Hom.hom c.pt.hom) = φ → ψ' = ψ := by
  classical
  let P := fun C : Under (CommRingCat.of B) ↦
    AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
      Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
        (Ideal.le_comap_map))
  have hs (C : ObjectProperty.FullSubcategory P) :
      ∃! τ : C.obj.right →+* A', τ.comp C.obj.hom.hom = φ :=
    existsUnique_henselization_stage_map B J C.obj.right C.obj.hom.hom
      C.property.1 C.property.2 A' I' φ hφ
  choose τ hτ huniq using hs
  let d : Cocone (ObjectProperty.ι P) :=
    { pt := Under.mk (CommRingCat.ofHom φ)
      ι :=
        { app := fun C ↦ Under.homMk (CommRingCat.ofHom (τ C))
            (by apply CommRingCat.hom_ext; exact hτ C)
          naturality := by
            intro C D g
            apply Under.UnderMorphism.ext
            apply CommRingCat.hom_ext
            change (τ D).comp g.hom.right.hom = τ C
            apply huniq C
            rw [RingHom.comp_assoc]
            have hg : g.hom.right.hom.comp C.obj.hom.hom = D.obj.hom.hom :=
              congrArg CommRingCat.Hom.hom (Under.w g.hom)
            rw [hg, hτ D] } }
  let H := hc.some
  let m := H.desc d
  have hm : m.right.hom.comp c.pt.hom.hom = φ :=
    congrArg CommRingCat.Hom.hom (Under.w m)
  refine ⟨m.right.hom, hm, ?_, ?_⟩
  · rw [Ideal.map_map, hm]
    exact hφ
  · intro ψ' hψ'
    let m' : c.pt ⟶ d.pt := Under.homMk (CommRingCat.ofHom ψ')
      (by apply CommRingCat.hom_ext; exact hψ')
    have heq : m' = m := by
      apply H.hom_ext
      intro C
      apply Under.UnderMorphism.ext
      apply CommRingCat.hom_ext
      change ψ'.comp (c.ι.app C).right.hom =
        m.right.hom.comp (c.ι.app C).right.hom
      have hstage (q : c.pt.right →+* A') (hq : q.comp c.pt.hom.hom = φ) :
          q.comp (c.ι.app C).right.hom = τ C := by
        apply huniq C
        rw [RingHom.comp_assoc]
        have hi : (c.ι.app C).right.hom.comp C.obj.hom.hom = c.pt.hom.hom :=
          congrArg CommRingCat.Hom.hom (Under.w (c.ι.app C))
        rw [hi, hq]
      rw [hstage ψ' hψ', hstage m.right.hom hm]
    exact congrArg (fun q ↦ q.right.hom) heq

end RingTheory
