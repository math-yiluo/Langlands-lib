/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Etale acyclicity of a strictly henselian local scheme

Source: Stacks Project, etale-cohomology.tex, Lemma Tag 03QO
(blueprint: lem-weil-pbc-strictly-henselian-etale-acyclic).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

/-- For a strictly henselian local ring, global sections on the small etale site are exact,
and all positive-degree etale cohomology objects vanish.
Source: Stacks Project, etale-cohomology.tex, Lemma Tag 03QO
(blueprint: lem-weil-pbc-strictly-henselian-etale-acyclic).
-/
theorem strictlyHenselian_etale_acyclic
    (R : Type u) [CommRing R] [IsLocalRing R]
    (hR : IsStrictlyHenselianLocalRing R) :
    exactFunctor
        (Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology (AlgebraicGeometry.Spec (.of R)))
          AddCommGrpCat.{u + 1})
        AddCommGrpCat.{u + 1}
        (Sheaf.Γ
          (AlgebraicGeometry.Scheme.smallEtaleTopology (AlgebraicGeometry.Spec (.of R)))
          AddCommGrpCat.{u + 1}) ∧
      ∀ (F : Sheaf
          (AlgebraicGeometry.Scheme.smallEtaleTopology (AlgebraicGeometry.Spec (.of R)))
          AddCommGrpCat.{u + 1}) (p : ℤ),
        1 ≤ p →
          IsZero
            ((AlgebraicGeometry.Etale.cohomology AddCommGrpCat.{u + 1}
              (AlgebraicGeometry.Spec (.of R)) p).obj
              ((DerivedCategory.singleFunctor
                (Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology
                  (AlgebraicGeometry.Spec (.of R))) AddCommGrpCat.{u + 1}) 0).obj F)) := by
  let : IsStrictlyHenselianLocalRing R := hR
  let G := Sheaf.Γ (Scheme.smallEtaleTopology (Spec (.of R))) AddCommGrpCat.{u + 1}
  let e := Sheaf.ΓNatIsoSheafSections (Scheme.smallEtaleTopology (Spec (.of R)))
    AddCommGrpCat.{u + 1} (Scheme.isTerminalEtaleTerminal R)
  have : G.PreservesEpimorphisms := Functor.PreservesEpimorphisms.of_iso e.symm
  have : G.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels G
  have : PreservesFiniteColimits G := G.preservesFiniteColimits_of_preservesHomology
  refine ⟨(exactFunctor_iff G).2 ⟨inferInstance, inferInstance⟩, ?_⟩
  intro F p hp
  have hz := DerivedCategory.isZero_of_isLE
    ((DerivedCategory.singleFunctor
      (Sheaf (Scheme.smallEtaleTopology (Spec (.of R))) AddCommGrpCat.{u + 1}) 0).obj F)
    0 p (by omega)
  exact (G.map_isZero hz).of_iso
    ((G.rightDerivedFunctorHomologyFunctorIso p).app _).symm
