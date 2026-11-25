/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NoetherianLocalModelTowerFiberSystem
import WeilConjectures.RingTheory.NoetherianLocalModelTowerFiberModuleColimit
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # The colimit of the explicit closed-fibre system

Source: Stacks Project, Algebra, Tag 00R7, proof by Noetherian approximation.
-/

@[expose] public section

universe u v w t

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Module

/-- The explicit closed-fibre systems have the expected colimit and scalar action.

Source: Stacks Project, Algebra, Tag 00R7, paragraph beginning with the colimit
of the maximal ideals, before the second application of Tag 00R6.
(blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-colimit)

Proof: The middle ring quotient cocone is already proved colimiting in
fiberSCoconeIsColimit, which constructs fiberAEquiv. The module-only comparison
fiber_module_colimit supplies an action with semilinear coprojections and an
additive comparison compatible with this fixed ring equivalence. Package these
equivalences to obtain the asserted comparison.

For uniqueness, the forgetful functors to types preserve these filtered ring and
group colimits. Thus every limit scalar and module element comes from a stage.
Directedness moves both representatives to one common stage. Naturality of the
coprojections identifies their limit images. Both actions' semilinearity equations
identify their scalar product with the image of the same stage scalar product.
Module.ext' and proof irrelevance identify their Module structures. This proves
uniqueness without using a module comparison or flatness hypothesis.
-/
theorem NoetherianLocalModelTower.fiber_colimit
    {R : Type u} {S : Type v} {S' : Type w} {M : Type t}
    [CommRing R] [CommRing S] [CommRing S'] [IsLocalRing R] [AddCommGroup M]
    [Algebra R S] [Algebra S S'] [Module S' M] [Module S M]
    [IsScalarTower S S' M]
    (X : NoetherianLocalModelTower R S S' M) :
    letI := X.preorder
    letI := X.commR
    letI := X.commS
    letI := X.localR
    letI := X.algRS
    letI := X.addN
    letI := X.moduleS
    let A := X.fiberA
    let B := X.fiberB
    let D := X.fiberD
    letI := X.fiberAct
    let ψ := X.fiberψ
    ∃! limitAct : Module (colimit B : CommRingCat.{max u v w})
      (colimit D : AddCommGrpCat.{max u v w t}),
    letI := limitAct
    (∀ (i : X.ι) (b : B.obj i) (x : D.obj i),
      (colimit.ι D i).hom (b • x) = (colimit.ι B i).hom b • (colimit.ι D i).hom x) ∧
    (∃
      (eA : (colimit A : CommRingCat.{max u v w}) ≃+*
        (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)))
      (eD : (colimit D : AddCommGrpCat.{max u v w t}) ≃+
        ((S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) ⊗[S] M)),
      letI := Module.compHom (colimit D : AddCommGrpCat.{max u v w t}) ψ
      ∀ a x, eD (a • x) = eA a • eD x) := by
  let := X.preorder
  let := X.nonempty
  let := X.directed
  let := X.commR
  let := X.commS
  let := X.localR
  let := X.algRS
  let := X.addN
  let := X.moduleS
  let := X.fiberAct
  obtain ⟨act, hsem, eD, heD⟩ := X.fiber_module_colimit
  refine ⟨act, ⟨hsem, ⟨X.fiberAEquiv, eD, heD⟩⟩, ?_⟩
  intro other hother
  obtain ⟨hsem', _⟩ := hother
  apply Module.ext' other act
  intro b x
  obtain ⟨i, bi, hbi⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget CommRingCat) (colimit.isColimit X.fiberB)) b
  let : PreservesColimit X.fiberD (forget AddCommGrpCat) :=
    preservesColimit_of_preserves_colimit_cocone
      (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit.{max u v w, t} X.fiberD)
      (Types.TypeMax.colimitCoconeIsColimit.{max u v w, t} (X.fiberD ⋙ forget AddCommGrpCat))
  obtain ⟨j, xj, hxj⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget AddCommGrpCat) (colimit.isColimit X.fiberD)) x
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  let bk := (X.fiberB.map (homOfLE hik)).hom bi
  let xk := (X.fiberD.map (homOfLE hjk)).hom xj
  have hbk : (colimit.ι X.fiberB k).hom bk = b := by
    exact (ConcreteCategory.congr_hom (colimit.w X.fiberB (homOfLE hik)) bi).trans hbi
  have hxk : (colimit.ι X.fiberD k).hom xk = x := by
    exact (ConcreteCategory.congr_hom (colimit.w X.fiberD (homOfLE hjk)) xj).trans hxj
  rw [← hbk, ← hxk]
  exact (hsem' k bk xk).symm.trans (hsem k bk xk)

end Module
