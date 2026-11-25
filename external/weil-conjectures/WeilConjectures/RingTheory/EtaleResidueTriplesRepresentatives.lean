/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.RingTheory.EtaleResidueTriplesFiltered

/-!
# EtaleResidueTriplesRepresentatives

Source: Stacks Project, Algebra, Tags 04GN and 04GP.
(blueprint: lem-weil-pbc-etale-triples-colimit-representative).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Algebra, Tags 04GN and 04GP.

Proof: The category of pointed etale algebras is filtered by
etaleResidueTriples_filtered_part, for arbitrary K and chi. Inside c.pt let S be
the elements represented by some coprojection. The identity triple represents zero
and one. Negatives stay represented at the same triple. For addition and multiplication,
filteredness supplies a common successor of the two representing triples; cocone
naturality represents the result there. Thus S is a subring of c.pt.
Every coprojection restricts to S, defining a cocone cS. The colimit universal
property gives d : c.pt -> S. The inclusion i : S -> c.pt satisfies i composed with d
= identity: both maps agree on every coprojection, so colimit uniqueness identifies
them. For any x, d(x) is in S and i(d(x))=x, hence x is represented. This argument
uses no small skeleton or preservation theorem for an underlying-set functor.
(blueprint: lem-weil-pbc-etale-triples-colimit-representative). -/
theorem etaleResidueTriples_colimit_representative
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (c : Cocone (etaleResidueTriplesRingDiagram R p K χ)) (hc : IsColimit c)
    (x : c.pt) : ∃ (t : EtaleResidueTriples R p K χ) (f : t.B),
      (c.ι.app t).hom f = x := by
  classical
  let := etaleResidueTriples_filtered_part R p K χ
  let D := etaleResidueTriplesRingDiagram R p K χ
  have lift_rep {t s : EtaleResidueTriples R p K χ} (a : t ⟶ s) (f : t.B) :
      (c.ι.app s).hom ((D.map a).hom f) = (c.ι.app t).hom f :=
    ConcreteCategory.congr_hom (c.w a) f
  let S : Subring c.pt :=
    { carrier := {y | ∃ (t : EtaleResidueTriples R p K χ) (f : t.B),
          (c.ι.app t).hom f = y}
      zero_mem' := ⟨⟨R, 𝟙 R, inferInstance, p, by simp, χ, by simp⟩, 0, map_zero _⟩
      one_mem' := ⟨⟨R, 𝟙 R, inferInstance, p, by simp, χ, by simp⟩, 1, map_one _⟩
      add_mem' := by
        rintro y z ⟨t, f, rfl⟩ ⟨s, g, rfl⟩
        obtain ⟨v, a, b, _⟩ := IsFilteredOrEmpty.cocone_objs t s
        refine ⟨v, (D.map a).hom f + (D.map b).hom g, ?_⟩
        rw [map_add, lift_rep a, lift_rep b]
      mul_mem' := by
        rintro y z ⟨t, f, rfl⟩ ⟨s, g, rfl⟩
        obtain ⟨v, a, b, _⟩ := IsFilteredOrEmpty.cocone_objs t s
        refine ⟨v, (D.map a).hom f * (D.map b).hom g, ?_⟩
        rw [map_mul, lift_rep a, lift_rep b]
      neg_mem' := by
        rintro y ⟨t, f, rfl⟩
        exact ⟨t, -f, map_neg _ _⟩ }
  let cS : Cocone D :=
    { pt := CommRingCat.of S
      ι :=
        { app := fun t ↦ CommRingCat.ofHom
            ((c.ι.app t).hom.codRestrict S (fun f ↦ ⟨t, f, rfl⟩))
          naturality := by
            intro t s a
            ext f
            apply Subtype.ext
            exact lift_rep a f } }
  let inc : cS.pt ⟶ c.pt := CommRingCat.ofHom S.subtype
  have hcomp : hc.desc cS ≫ inc = 𝟙 c.pt := by
    apply hc.hom_ext
    intro t
    calc
      _ = (c.ι.app t ≫ hc.desc cS) ≫ inc := (Category.assoc _ _ _).symm
      _ = cS.ι.app t ≫ inc := congrArg (fun f ↦ f ≫ inc) (hc.fac cS t)
      _ = c.ι.app t ≫ 𝟙 c.pt := by ext f; rfl
  have hx : ((hc.desc cS ≫ inc).hom x) = x :=
    ConcreteCategory.congr_hom hcomp x
  exact hx ▸ ((hc.desc cS).hom x).property

end AlgebraicGeometry.Scheme
