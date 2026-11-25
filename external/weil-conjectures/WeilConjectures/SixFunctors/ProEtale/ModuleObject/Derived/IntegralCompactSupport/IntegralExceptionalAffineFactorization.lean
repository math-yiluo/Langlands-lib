/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralBrownAdjoint
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverBase
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestriction

/-!
# Geometric and adjoint factorization on one affine chart

Source: blueprint main-20261015, sk-thm-int-restriction, General f paragraph,
and sk-thm-int-restriction-glue.proof.md, paragraph (2).
(blueprint: lem-sfb-integral-exceptional-affine-factorization).
-/

@[expose] public section
set_option linter.privateModule false

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport

variable {X Y : Scheme.{u}}

private noncomputable def liftAdjunction
    {C D : Type*} [Category C] [Category D] (P : ObjectProperty C) (Q : ObjectProperty D)
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (hF : ∀ A : P.FullSubcategory, Q (F.obj A.obj))
    (hG : ∀ B : Q.FullSubcategory, P (G.obj B.obj)) :
    Q.lift (P.ι ⋙ F) hF ⊣ P.lift (Q.ι ⋙ G) hG :=
  adj.restrictFullyFaithful P.fullyFaithfulι Q.fullyFaithfulι (Iso.refl _) (Iso.refl _)

private noncomputable def liftIso
    {C D : Type*} [Category C] [Category D] (P : ObjectProperty D)
    {F G : C ⥤ P.FullSubcategory} (e : F ⋙ P.ι ≅ G ⋙ P.ι) : F ≅ G :=
  NatIso.ofComponents (fun A ↦ P.isoMk (e.app A)) (by
    intro A B m
    apply ObjectProperty.hom_ext
    exact e.hom.naturality m)

private noncomputable def space (k : Type u) [Field k] (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))] : Spaces k :=
  ⟨Over.mk (T ↘ Spec (.of k)),
    ⟨inferInstanceAs (IsSeparated (T ↘ Spec (.of k))),
      inferInstanceAs (LocallyOfFiniteType (T ↘ Spec (.of k))),
      inferInstanceAs (QuasiCompact (T ↘ Spec (.of k)))⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
