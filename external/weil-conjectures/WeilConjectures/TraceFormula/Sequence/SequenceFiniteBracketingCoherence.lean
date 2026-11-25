/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Supporting.QuotientSystemMixedCoherenceData

/-! # A component of strict quotient-system coherence

Source: Stacks Project, sites-cohomology.tex, Tag 0D6D.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe t u a v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  integralComparisonSequenceScalarModel
attribute [local instance 5000] coefficientSequenceEssentiallySmall
attribute [local instance 6000] HasDerivedCategory.standard
attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  finiteSystemSequenceSmall finiteSystemSiteSmall
attribute [local irreducible] HasDerivedCategory.standard

section Normalization

variable (D : Scheme.{t} → Type a) [∀ X, Category.{v} (D X)]
  (U : ∀ {X Y : Scheme.{t}}, (X ⟶ Y) → (D Y ⥤ D X))
  (c : ∀ {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z), U (f ≫ g) ≅ U g ⋙ U f)
  (e : ∀ X : Scheme.{t}, U (𝟙 X) ≅ 𝟭 (D X))

private def sequenceNormalFunctor {X : Scheme.{t}} :
    ∀ {Y : Scheme.{t}}, Quiver.Path X Y → (D Y ⥤ D X)
  | _, .nil => 𝟭 _
  | _, .cons p f => U f ⋙ sequenceNormalFunctor p

private def sequenceNormalMap {X : Scheme.{t}} :
    ∀ {Y : Scheme.{t}} (p : Quiver.Path X Y),
      U (composePath p) ⟶ sequenceNormalFunctor D U p
  | _, .nil => (e X).hom
  | _, .cons p f => (c (composePath p) f).hom ≫
      Functor.whiskerLeft (U f) (sequenceNormalMap p)

private theorem sequenceNormalFunctor_comp {X Y Z : Scheme.{t}}
    (p : Quiver.Path X Y) (q : Quiver.Path Y Z) :
    sequenceNormalFunctor D U (p.comp q) =
      sequenceNormalFunctor D U q ⋙ sequenceNormalFunctor D U p := by
  induction q with
  | nil => rfl
  | cons q f ih => exact congrArg (fun F ↦ U f ⋙ F) ih

private theorem sequenceWhiskerLeft_eqToHom {X Y Z : Scheme.{t}}
    (F : D Z ⥤ D Y) {G H : D Y ⥤ D X} (h : G = H) :
    Functor.whiskerLeft F (eqToHom h) = eqToHom (congrArg (fun G ↦ F ⋙ G) h) := by
  cases h
  simp

private theorem sequenceCompositor_transport {X Y Z : Scheme.{t}}
    {f f' : X ⟶ Y} (h : f = f') (g : Y ⟶ Z) :
    (c f g).hom ≫ Functor.whiskerLeft (U g) (eqToHom (congrArg (fun f ↦ U f) h)) =
      eqToHom (congrArg (fun f ↦ U (f ≫ g)) h) ≫ (c f' g).hom := by
  cases h
  simp

private theorem sequenceWhisker_transport {X Y Z : Scheme.{t}}
    {F F' : D Z ⥤ D Y} {G G' : D Y ⥤ D X}
    {A : D Z ⥤ D Y} {B : D Y ⥤ D X} (α : B ⟶ G) (β : A ⟶ F)
    (hG : G = G') (hF : F = F') :
    (Functor.whiskerLeft A α ≫ Functor.whiskerRight β G) ≫
        eqToHom (congrArg₂ (fun F G ↦ F ⋙ G) hF hG) =
      Functor.whiskerLeft A (α ≫ eqToHom hG) ≫
        Functor.whiskerRight (β ≫ eqToHom hF) G' := by
  cases hG
  cases hF
  simp

private theorem sequenceNormalMap_comp
    (hA : ∀ {T X Y Z : Scheme.{t}} (f : Z ⟶ Y) (g : Y ⟶ X) (h : X ⟶ T),
      (c (f ≫ g) h).hom ≫ Functor.whiskerLeft (U h) (c f g).hom =
        eqToHom (congrArg (fun f ↦ U f) (Category.assoc f g h)) ≫
          (c f (g ≫ h)).hom ≫ Functor.whiskerRight (c g h).hom (U f))
    (hR : ∀ {X Y : Scheme.{t}} (f : X ⟶ Y),
      (c f (𝟙 Y)).hom ≫ Functor.whiskerRight (e Y).hom (U f) =
        eqToHom (congrArg (fun f ↦ U f) (Category.comp_id f)))
    {X Y Z : Scheme.{t}} (p : Quiver.Path X Y) (q : Quiver.Path Y Z) :
    sequenceNormalMap D U c e (p.comp q) ≫ eqToHom (sequenceNormalFunctor_comp D U p q) =
      eqToHom (congrArg (fun f ↦ U f) (composePath_comp p q)) ≫
        (c (composePath p) (composePath q)).hom ≫
        Functor.whiskerLeft (U (composePath q)) (sequenceNormalMap D U c e p) ≫
        Functor.whiskerRight (sequenceNormalMap D U c e q) (sequenceNormalFunctor D U p) := by
  induction q with
  | nil =>
    dsimp [sequenceNormalMap, sequenceNormalFunctor]
    rw [Functor.whiskerLeft_comp_whiskerRight]
    simp only [← Category.assoc, hR]
    simp
    rfl
  | cons q f ih =>
    change ((c (composePath (p.comp q)) f).hom ≫
      Functor.whiskerLeft (U f) (sequenceNormalMap D U c e (p.comp q))) ≫
        eqToHom (congrArg (fun F ↦ U f ⋙ F) (sequenceNormalFunctor_comp D U p q)) = _
    rw [← sequenceWhiskerLeft_eqToHom D (U f) (sequenceNormalFunctor_comp D U p q),
      Category.assoc, ← Functor.whiskerLeft_comp, ih]
    simp only [Functor.whiskerLeft_comp, ← Category.assoc]
    rw [sequenceCompositor_transport D U c (composePath_comp p q) f]
    simp only [Category.assoc]
    rw [← Category.assoc (c (composePath p ≫ composePath q) f).hom, hA]
    simp only [Category.assoc, eqToHom_trans_assoc]
    have hs :
        Functor.whiskerRight (c (composePath q) f).hom (U (composePath p)) ≫
            Functor.whiskerLeft (U f)
              (Functor.whiskerLeft (U (composePath q)) (sequenceNormalMap D U c e p)) =
          Functor.whiskerLeft (U (composePath q ≫ f)) (sequenceNormalMap D U c e p) ≫
            Functor.whiskerRight (c (composePath q) f).hom (sequenceNormalFunctor D U p) :=
      (Functor.whiskerLeft_comp_whiskerRight (c (composePath q) f).hom
        (sequenceNormalMap D U c e p)).symm
    rw [← Category.assoc (Functor.whiskerRight (c (composePath q) f).hom
      (U (composePath p))), hs]
    simp only [sequenceNormalMap, Functor.whiskerRight_comp, Category.assoc]
    rfl

end Normalization

/-- Source: Stacks Project, sites-cohomology.tex, Tag 0D6D.
(blueprint: lem-trf-sequence-finite-bracketing-coherence).
Proof: Define the right-associated word of a path and its comparison recursively, using the
identity comparison for the empty path. Induction on concatenation proves that its comparison is
the composite comparison followed by the two whiskered path comparisons: the empty case is the
right-unit law and the successor case is three-arrow associativity. The left-unit law treats
singleton paths. Induct on a binary bracketing to identify its comparison with this path
comparison. The functors of both bracketings identify with the same right-associated functor;
compose these identifications and cancel the second one to obtain the asserted equality. Equality
transports commute with whiskering by equality induction. -/
theorem sequenceFiniteCoherence
    (D : Scheme.{t} → Type a) [∀ X, Category.{v} (D X)]
    (U : ∀ {X Y : Scheme.{t}}, (X ⟶ Y) → (D Y ⥤ D X))
    (c : ∀ {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z), U (f ≫ g) ≅ U g ⋙ U f)
    (e : ∀ X : Scheme.{t}, U (𝟙 X) ≅ 𝟭 (D X))
    (hA : ∀ {T X Y Z : Scheme.{t}} (f : Z ⟶ Y) (g : Y ⟶ X) (h : X ⟶ T),
      (c (f ≫ g) h).hom ≫ Functor.whiskerLeft (U h) (c f g).hom =
        eqToHom (congrArg (fun f ↦ U f) (Category.assoc f g h)) ≫
          (c f (g ≫ h)).hom ≫ Functor.whiskerRight (c g h).hom (U f))
    (hL : ∀ {X Y : Scheme.{t}} (f : X ⟶ Y),
      (c (𝟙 X) f).hom ≫ Functor.whiskerLeft (U f) (e X).hom =
        eqToHom (congrArg (fun f ↦ U f) (Category.id_comp f)))
    (hR : ∀ {X Y : Scheme.{t}} (f : X ⟶ Y),
      (c f (𝟙 Y)).hom ≫ Functor.whiskerRight (e Y).hom (U f) =
        eqToHom (congrArg (fun f ↦ U f) (Category.comp_id f)))
    {X Y : Scheme.{t}} {p : Quiver.Path X Y} (a b : IntegralQuotientBracketing p) :
    ∃ h : integralQuotientBracketFunctor D U a = integralQuotientBracketFunctor D U b,
      integralQuotientBracketComparison D U c e a ≪≫ eqToIso h =
        integralQuotientBracketComparison D U c e b := by
  have hn : ∀ {X Y : Scheme.{t}} {p : Quiver.Path X Y}
      (b : IntegralQuotientBracketing p),
      ∃ h : integralQuotientBracketFunctor D U b = sequenceNormalFunctor D U p,
        (integralQuotientBracketComparison D U c e b).hom ≫ eqToHom h =
          sequenceNormalMap D U c e p := by
    intro X Y p b
    induction b with
    | nil X =>
      refine ⟨rfl, ?_⟩
      simp [integralQuotientBracketComparison, sequenceNormalMap]
    | single f =>
      refine ⟨rfl, ?_⟩
      simpa only [integralQuotientBracketComparison, sequenceNormalMap,
        Quiver.Hom.toPath, sequenceNormalFunctor, composePath,
        eqToIso.hom, eqToHom_refl, Category.comp_id] using (hL f).symm
    | @comp X Y Z p q a b iha ihb =>
      obtain ⟨ha, hca⟩ := iha
      obtain ⟨hb, hcb⟩ := ihb
      let h := (congrArg₂ (fun F G ↦ F ⋙ G) hb ha).trans
        (sequenceNormalFunctor_comp D U p q).symm
      refine ⟨h, ?_⟩
      apply (cancel_mono (eqToHom (sequenceNormalFunctor_comp D U p q))).mp
      simp only [Category.assoc, eqToHom_trans]
      rw [sequenceNormalMap_comp D U c e hA hR p q]
      have hw := sequenceWhisker_transport D
        (integralQuotientBracketComparison D U c e a).hom
        (integralQuotientBracketComparison D U c e b).hom ha hb
      rw [hca, hcb] at hw
      simpa only [integralQuotientBracketComparison, Iso.trans_hom, eqToIso.hom,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Category.assoc] using
        congrArg (fun k ↦
          eqToHom (congrArg (fun f ↦ U f) (composePath_comp p q)) ≫
            (c (composePath p) (composePath q)).hom ≫ k) hw
  obtain ⟨ha, hca⟩ := hn a
  obtain ⟨hb, hcb⟩ := hn b
  refine ⟨ha.trans hb.symm, ?_⟩
  apply Iso.ext
  apply (cancel_mono (eqToHom hb)).mp
  simpa only [Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans] using
    hca.trans hcb.symm

end WeilConjectures
