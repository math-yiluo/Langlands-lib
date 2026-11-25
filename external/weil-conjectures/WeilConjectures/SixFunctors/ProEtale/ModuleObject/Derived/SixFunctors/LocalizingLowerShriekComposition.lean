/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementIdentity

/-!
# Composition of rational lower shriek on localizing constructible categories

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-comp-composition,
clause (1), rational cases, and its proof, paragraphs "The composition isomorphism" and
"Canonicity and associativity"
(blueprint: lem-sfb-localizing-lower-shriek-composition).

The statement is recorded here as the canonical project interface for this composition.

The coefficients are exactly a finite subextension or the finite-subextension-valued
condensed algebraic closure. The functors are the existing restrictions of `Rp_* D(j_!)`.
Compatibility is expressed using the canonical refinement components of the recorded
compactification cocycle. Every triple of compactifications is allowed, including
nondense ones. Common dense refinements and the cocycle law identify the final equation
with compatibility with all compactification comparison isomorphisms.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private noncomputable def liftCompactificationIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c d : Compactification.BoundaryCompactification f)
    (hc : ∀ K, localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
      ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
    (hd : ∀ K, localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
      ((rightDerivedLowerShriekOfCompactification Λ d.obj.obj).obj K))
    (e : compactificationLocalizingCandidate Λ c ≅ compactificationLocalizingCandidate Λ d) :
    localizingLowerShriek Λ c.obj.obj hc ≅ localizingLowerShriek Λ d.obj.obj hd :=
  NatIso.ofComponents (fun K ↦ (localizingClosureProEtale Λ Y).isoMk (e.app K))
    (fun v ↦ by
      apply (localizingClosureProEtale Λ Y).ι.map_injective
      exact e.hom.naturality v)

private theorem liftCompactificationIso_cocycle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (a b c : Compactification.BoundaryCompactification f)
    (ha : ∀ K, localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
      ((rightDerivedLowerShriekOfCompactification Λ a.obj.obj).obj K))
    (hb : ∀ K, localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
      ((rightDerivedLowerShriekOfCompactification Λ b.obj.obj).obj K))
    (hc : ∀ K, localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
      ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
    (e₁ : compactificationLocalizingCandidate Λ a ≅ compactificationLocalizingCandidate Λ b)
    (e₂ : compactificationLocalizingCandidate Λ b ≅ compactificationLocalizingCandidate Λ c)
    (e₃ : compactificationLocalizingCandidate Λ a ≅ compactificationLocalizingCandidate Λ c)
    (h : e₁ ≪≫ e₂ = e₃) :
    liftCompactificationIso Λ a b ha hb e₁ ≪≫ liftCompactificationIso Λ b c hb hc e₂ =
      liftCompactificationIso Λ a c ha hc e₃ := by
  subst e₃
  apply Iso.ext
  apply NatTrans.ext
  funext K
  rfl

private theorem transportComposition
    {C D T : Type*} [Category C] [Category D] [Category T]
    {I J L : Type*} (F : I → C ⥤ D) (G : J → D ⥤ T) (H : L → C ⥤ T)
    (φ : ∀ a b, F a ≅ F b) (ψ : ∀ a b, G a ≅ G b) (χ : ∀ a b, H a ≅ H b)
    (hφ : ∀ a b c, φ a b ≪≫ φ b c = φ a c)
    (hψ : ∀ a b c, ψ a b ≪≫ ψ b c = ψ a c)
    (hχ : ∀ a b c, χ a b ≪≫ χ b c = χ a c)
    (a₀ : I) (b₀ : J) (c₀ : L) (e : F a₀ ⋙ G b₀ ≅ H c₀) :
    ∃ α : ∀ a b c, F a ⋙ G b ≅ H c,
      ∀ a b c a' b' c' K,
        (G b).map ((φ a a').hom.app K) ≫
          (ψ b b').hom.app ((F a').obj K) ≫ (α a' b' c').hom.app K =
        (α a b c).hom.app K ≫ (χ c c').hom.app K := by
  let α := fun a b c ↦
    Functor.isoWhiskerRight (φ a a₀) (G b) ≪≫
      Functor.isoWhiskerLeft (F a₀) (ψ b b₀) ≪≫ e ≪≫ χ c₀ c
  refine ⟨α, ?_⟩
  intro a b c a' b' c' K
  have hF := congrArg (fun t ↦ t.hom.app K) (hφ a a' a₀)
  have hG := congrArg (fun t ↦ t.hom.app ((F a₀).obj K)) (hψ b b' b₀)
  have hH := congrArg (fun t ↦ t.hom.app K) (hχ c₀ c c')
  dsimp only [Iso.trans_hom, NatTrans.comp_app] at hF hG hH
  dsimp only [α, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [Category.assoc]
  rw [← Category.assoc ((ψ b b').hom.app _) ((G b').map _) _,
    ← (ψ b b').hom.naturality]
  simp only [← Functor.map_comp_assoc, hF, Category.assoc]
  rw [← Category.assoc ((ψ b b').hom.app _) ((ψ b' b₀).hom.app _) _, hG]
  rw [hH]

/-- There is a natural composition isomorphism on the ordinary localizing closures for
rational condensed coefficients, compatible with change of compactification. The witnesses
`hf`, `hg`, `hgf` only certify preservation by the actual ambient compactification functors;
`localizingLowerShriek` uses those same objects and maps. The equation is an equality in the
ambient derived category, hence also in its full localizing subcategory. Its refinement
maps are exactly those used to normalize the comparisons in
`compactification_coherence_cocycle`, rather than arbitrary isomorphisms of their endpoints.

Source: blueprint proposition-composition-base-change-rf-shriek--1, clause (1), rational cases, and
its proof (blueprint: proposition-composition-base-change-rf-shriek--1).

Proof: obtain preservation from compactification_localizing. Construct an isomorphism
on one compactification triple using the model lemma, then lift it to the full localizing
target. Conjugate it by the three compactification comparison cocycles to define every
other component. Naturality of the middle comparison and the three cocycle equations
give the simultaneous comparison square. The identity-refinement law identifies each
comparison to a dense model with the prescribed canonical refinement component,
so this square is exactly the equation displayed below. -/
theorem exists_localizingLowerShriekComposition
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (_hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    [QuasiCompact (Z ↘ Spec (.of k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] :
    ∃ (hf : ∀ (c : Compactification.BoundaryCompactification f) K,
          localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
            ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
      (hg : ∀ (c : Compactification.BoundaryCompactification g) K,
          localizingClosureProEtale Λ Y K → localizingClosureProEtale Λ Z
            ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
      (hgf : ∀ (c : Compactification.BoundaryCompactification (f ≫ g)) K,
          localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Z
            ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K)),
      ∃ α : ∀ (cf : Compactification.BoundaryCompactification f)
          (cg : Compactification.BoundaryCompactification g)
          (cgf : Compactification.BoundaryCompactification (f ≫ g)),
          localizingLowerShriek Λ cf.obj.obj (hf cf) ⋙
              localizingLowerShriek Λ cg.obj.obj (hg cg) ≅
            localizingLowerShriek Λ cgf.obj.obj (hgf cgf),
        ∀ (cf : Compactification.BoundaryCompactification f)
          (cg : Compactification.BoundaryCompactification g)
          (cgf : Compactification.BoundaryCompactification (f ≫ g))
          (df : Compactification.DenseBoundaryCompactification f)
          (dg : Compactification.DenseBoundaryCompactification g)
          (dgf : Compactification.DenseBoundaryCompactification (f ≫ g))
          (rf : df.obj ⟶ cf) (rg : dg.obj ⟶ cg) (rgf : dgf.obj ⟶ cgf)
          (K : (localizingClosureProEtale Λ X).FullSubcategory),
          (rightDerivedLowerShriekOfCompactification Λ cg.obj.obj).map
              (compactificationRefinementComponent Λ rf K.obj) ≫
            compactificationRefinementComponent Λ rg
              ((rightDerivedLowerShriekOfCompactification Λ df.obj.obj.obj).obj K.obj) ≫
            ((α df.obj dg.obj dgf.obj).hom.app K).hom =
          ((α cf cg cgf).hom.app K).hom ≫
            compactificationRefinementComponent Λ rgf K.obj := by
  classical
  have hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ := by
    rcases _hΛ with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, h⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of k))
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated (Z ↘ Spec (.of k))
  have hf := fun c ↦ (compactification_localizing Λ ℓ k f c hΛ).1
  have hg := fun c ↦ (compactification_localizing Λ ℓ k g c hΛ).1
  have hgf := fun c ↦ (compactification_localizing Λ ℓ k (f ≫ g) c hΛ).1
  obtain ⟨φf, hρf, hnf, _, hcf⟩ := compactification_coherence_cocycle Λ ℓ hΛ k f
  obtain ⟨φg, hρg, hng, _, hcg⟩ := compactification_coherence_cocycle Λ ℓ hΛ k g
  obtain ⟨φgf, hρgf, hngf, _, hcgf⟩ :=
    compactification_coherence_cocycle Λ ℓ hΛ k (f ≫ g)
  let F := fun (c : Compactification.BoundaryCompactification f) ↦
    localizingLowerShriek Λ c.obj.obj (hf c)
  let G := fun (c : Compactification.BoundaryCompactification g) ↦
    localizingLowerShriek Λ c.obj.obj (hg c)
  let H := fun (c : Compactification.BoundaryCompactification (f ≫ g)) ↦
    localizingLowerShriek Λ c.obj.obj (hgf c)
  let φ := fun c d ↦ liftCompactificationIso Λ c d (hf c) (hf d) (φf c d)
  let ψ := fun c d ↦ liftCompactificationIso Λ c d (hg c) (hg d) (φg c d)
  let χ := fun c d ↦ liftCompactificationIso Λ c d (hgf c) (hgf d) (φgf c d)
  have hcφ : ∀ a b c, φ a b ≪≫ φ b c = φ a c := by
    intro a b c
    exact liftCompactificationIso_cocycle Λ a b c (hf a) (hf b) (hf c)
      (φf a b) (φf b c) (φf a c) (hcf a b c)
  have hcψ : ∀ a b c, ψ a b ≪≫ ψ b c = ψ a c := by
    intro a b c
    exact liftCompactificationIso_cocycle Λ a b c (hg a) (hg b) (hg c)
      (φg a b) (φg b c) (φg a c) (hcg a b c)
  have hcχ : ∀ a b c, χ a b ≪≫ χ b c = χ a c := by
    intro a b c
    exact liftCompactificationIso_cocycle Λ a b c (hgf a) (hgf b) (hgf c)
      (φgf a b) (φgf b c) (φgf a c) (hcgf a b c)
  have hbase : ∃ cf cg cgf, Nonempty (F cf ⋙ G cg ≅ H cgf) := by
    obtain ⟨cf, cg, cgf, ⟨e⟩⟩ :=
      exists_localizingLowerShriekComposition_model Λ ℓ E _hΛ k f g
    refine ⟨cf, cg, cgf, ⟨NatIso.ofComponents
      (fun K ↦ (localizingClosureProEtale Λ Z).isoMk (e.app K)) ?_⟩⟩
    intro K L v
    apply (localizingClosureProEtale Λ Z).ι.map_injective
    exact e.hom.naturality v
  obtain ⟨cf₀, cg₀, cgf₀, ⟨e⟩⟩ := hbase
  obtain ⟨α, hα⟩ := transportComposition F G H φ ψ χ hcφ hcψ hcχ cf₀ cg₀ cgf₀ e
  refine ⟨hf, hg, hgf, α, ?_⟩
  intro cf cg cgf df dg dgf rf rg rgf K
  have hrf := hnf cf df.obj df rf (𝟙 df.obj) K
  have hrg := hng cg dg.obj dg rg (𝟙 dg.obj) ((F df.obj).obj K)
  have hrgf := hngf cgf dgf.obj dgf rgf (𝟙 dgf.obj) K
  have hidf := compactificationRefinementComponent_id Λ ℓ k hΛ f df K.obj
  have hidg := compactificationRefinementComponent_id Λ ℓ k hΛ g dg
    ((F df.obj).obj K).obj
  have hidgf := compactificationRefinementComponent_id Λ ℓ k hΛ (f ≫ g) dgf K.obj
  rw [hidf] at hrf
  rw [hidg] at hrg
  rw [hidgf] at hrgf
  replace hrf := (Category.comp_id _).symm.trans hrf
  replace hrg := (Category.comp_id _).symm.trans hrg
  replace hrgf := (Category.comp_id _).symm.trans hrgf
  erw [← hrf, ← hrg, ← hrgf]
  exact congrArg (fun t ↦ t.hom)
    (hα cf cg cgf df.obj dg.obj dgf.obj K)

end AlgebraicGeometry.ProEtale.CondensedRing
