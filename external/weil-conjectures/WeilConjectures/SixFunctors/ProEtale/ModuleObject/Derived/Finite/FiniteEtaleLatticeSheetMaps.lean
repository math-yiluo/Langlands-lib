/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.ContinuousLatticeIntersectionSupplement

/-! # Actual sheet and trace-image inclusions

Source: blueprint, stratified lattice proof, "Pushing down by the trace".
(blueprint: def-sfb-finite-etale-lattice-sheet-maps)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]

/-- Restrict the supplied integral lattice embedding to an actual sheet and
identify its rational target using the specified composition equation.
Source: blueprint, stratified lattice trace proof, Local computation, paragraph 1.
(blueprint: def-sfb-finite-etale-lattice-sheet-maps) -/
def finiteEtaleLatticeSheetEmbedding (a : R ⟶ S) [IsMonHom a]
    {X U Y : Scheme.{u}}
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X))
    (p : U ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj R U))
    (e : (Mod.extendScalars (coefficientMap a U)).obj M ≅ (upperStar S p).obj P)
    (g : Y ⟶ X) (t : Y ⟶ U) (w : t ≫ p = g) :
    (upperStar R t).obj M ⟶
      (Mod.comap (coefficientMap a Y)).obj ((upperStar S g).obj P) :=
  (upperStar R t).map (latticeIntegralEmbedding a X P p M e) ≫
    (comapUpperStarIso a t).inv.app ((upperStar S p).obj P) ≫
      (Mod.comap (coefficientMap a Y)).map
        (((eqToIso (congrArg (upperStar S) w)).symm ≪≫
          upperStarComp S t p).inv.app P)

/-- Pull back the actual inclusion of the integral trace image and normalize
its target by the canonical restriction-of-scalars comparison.
Source: blueprint, stratified lattice trace proof, Local computation, paragraph 1.
(blueprint: def-sfb-finite-etale-lattice-sheet-maps) -/
def finiteEtaleTraceImageEmbedding (a : R ⟶ S) [IsMonHom a]
    {X U Y : Scheme.{u}}
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X))
    (p : U ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj R U))
    (e : (Mod.extendScalars (coefficientMap a U)).obj M ≅ (upperStar S p).obj P)
    (τ : (lowerStar S p).obj ((upperStar S p).obj P) ⟶ P) (g : Y ⟶ X) :
    (upperStar R g).obj
        (image (latticePushedEmbedding a X P p M e ≫
          (Mod.comap (coefficientMap a X)).map τ)) ⟶
      (Mod.comap (coefficientMap a Y)).obj ((upperStar S g).obj P) :=
  (upperStar R g).map
      (image.ι (latticePushedEmbedding a X P p M e ≫
        (Mod.comap (coefficientMap a X)).map τ)) ≫
    (comapUpperStarIso a g).inv.app P

/-- The normalized pulled-back image inclusion is monic.
Source: exact module pullback and the categorical image inclusion.
(blueprint: def-sfb-finite-etale-lattice-sheet-maps)

Proof. Pullback preserves monomorphisms, and the normalization is an isomorphism. -/
instance finiteEtaleTraceImageEmbedding_mono (a : R ⟶ S) [IsMonHom a]
    {X U Y : Scheme.{u}}
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X))
    (p : U ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj R U))
    (e : (Mod.extendScalars (coefficientMap a U)).obj M ≅ (upperStar S p).obj P)
    (τ : (lowerStar S p).obj ((upperStar S p).obj P) ⟶ P) (g : Y ⟶ X) :
    Mono (finiteEtaleTraceImageEmbedding a P p M e τ g) := by
  unfold finiteEtaleTraceImageEmbedding
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
