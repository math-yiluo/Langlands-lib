/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralRealizationAssemblyData
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus

/-! # Realization squares for canonical expression pairs

Source: blueprint fix-prop-coherence, strict-system expression realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Naturality of the normalized open comparison on its good domain.
Source: blueprint fix-prop-coherence, open reconstruction normalization.
(blueprint: lem-sf-integral-open-realization-naturality).

Proof: write the openNormalization equations at M and N. Naturality of the actual
counit moves s past the reconstruction map; naturality of openReduction moves its
limit map past L(s). The reconstruction unit is natural and invertible on the
completed open images, and the counits at the normalized systems are invertible.
Cancel those factors to get the displayed square. Empty opens and zero objects
satisfy the same triangle identities. No expression recursion occurs here. -/
theorem integralOpenRealizationNaturality
    (o : Operations l E) (a : AmbientModels l E o)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] (hq : QuasiCompact j)
    (M N : System l E U) (hM : Good l E U M) (hN : Good l E U N)
    (hJM : Good l E V ((Operations.shriek l E o j).obj M))
    (hJN : Good l E V ((Operations.shriek l E o j).obj N)) (s : M ⟶ N) :
    (coefficientSequenceLimit l E V).map ((Operations.shriek l E o j).map s) ≫
      (a.openRealization j hq N hN hJN).hom =
    (a.openRealization j hq M hM hJM).hom ≫
      (ringedOpen l E j).map ((coefficientSequenceLimit l E U).map s) := by
  let := hq
  let L := coefficientSequenceLimit l E U
  let R := (calculus l E U).reduction
  let LV := coefficientSequenceLimit l E V
  let RV := (calculus l E V).reduction
  let J := Operations.shriek l E o j
  let B : Integral l E U ⥤ Integral l E V := ringedOpen l E j
  let F := J ⋙ LV
  let G := L ⋙ B
  let ε := (calculus l E U).adjunction.counit
  let η := (calculus l E V).adjunction.unit
  let cM := (a.openRealization j hq M hM hJM).hom
  let cN := (a.openRealization j hq N hN hJN).hom
  let α : (L ⋙ R) ⋙ F ⟶ G ⋙ RV ⋙ LV :=
    Functor.whiskerLeft L (Functor.whiskerRight
      (a.realizationModel.openReduction l E j) LV)
  have : IsIso (ε.app M) :=
    ((purNormalizedReconstructionOfScheme l E U (calculus l E U)).1 M hM.1).2
  have : IsIso (η.app (LV.obj (J.obj N))) :=
    (purNormalizedReconstructionOfScheme l E V (calculus l E V)).2 _
      (((purNormalizedReconstructionOfScheme l E V (calculus l E V)).1 _ hJN.1).1)
  have : IsIso (cN ≫ η.app (G.obj N)) := by
    have hn : cN ≫ η.app (G.obj N) =
        η.app (LV.obj (J.obj N)) ≫ (RV ⋙ LV).map cN := by
      exact η.naturality cN
    rw [hn]
    infer_instance
  have : IsIso (η.app (G.obj N)) := IsIso.of_isIso_comp_left cN _
  have hnM : F.map (ε.app M) ≫ cM ≫ η.app (G.obj M) = α.app M :=
    a.openNormalization j M hM hJM
  have hnN : F.map (ε.app N) ≫ cN ≫ η.app (G.obj N) = α.app N :=
    a.openNormalization j N hN hJN
  change F.map s ≫ cN = cM ≫ G.map s
  apply (cancel_epi (F.map (ε.app M))).1
  apply (cancel_mono (η.app (G.obj N))).1
  simp only [Category.assoc]
  calc
    F.map (ε.app M) ≫ F.map s ≫ cN ≫ η.app (G.obj N) =
        F.map ((L ⋙ R).map s) ≫ F.map (ε.app N) ≫ cN ≫ η.app (G.obj N) := by
      have hn : ε.app M ≫ s = (L ⋙ R).map s ≫ ε.app N := (ε.naturality s).symm
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun q ↦ F.map q ≫ cN ≫ η.app (G.obj N)) hn
    _ = F.map ((L ⋙ R).map s) ≫ α.app N := by rw [hnN]
    _ = α.app M ≫ (G ⋙ RV ⋙ LV).map s := by
      exact α.naturality s
    _ = F.map (ε.app M) ≫ cM ≫ η.app (G.obj M) ≫ (G ⋙ RV ⋙ LV).map s := by
      simpa only [Category.assoc] using
        congrArg (fun q ↦ q ≫ (G ⋙ RV ⋙ LV).map s) hnM.symm
    _ = F.map (ε.app M) ≫ cM ≫ G.map s ≫ η.app (G.obj N) := by
      have ht := η.naturality (G.map s)
      change G.map s ≫ η.app (G.obj N) =
        η.app (G.obj M) ≫ (G ⋙ RV ⋙ LV).map s at ht
      simpa only [Category.assoc] using
        congrArg (fun q ↦ F.map (ε.app M) ≫ cM ≫ q) ht.symm

end WeilConjectures.IntegralSystemRealization
