/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.ContinuousLatticeIntersectionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLatticeSumFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteEtaleTraceFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousFiniteEtaleLatticeSheetCharts
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteEtaleTraceSheetRanges
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # Continuous finite lattice sum charts of the integral trace image

Source: blueprint, stratified lattice proof, "Pushing down by the trace".
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] continuousRingModuleEquivalence

private theorem additive_equiv_of_equal_ranges
    {M N V : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup V]
    (f : M →+ V) (g : N →+ V) (hf : Function.Injective f) (hg : Function.Injective g)
    (hr : Set.range f = Set.range g) :
    ∃ e : M ≃+ N, ∀ x, g (e x) = f x := by
  classical
  have hx (x : M) : ∃ y, g y = f x := by
    have h : f x ∈ Set.range g := by rw [← hr]; exact ⟨x, rfl⟩
    exact h
  let k : M → N := fun x ↦ (hx x).choose
  have hk (x : M) : g (k x) = f x := (hx x).choose_spec
  let h : M →+ N :=
    { toFun := k
      map_zero' := by apply hg; rw [hk, map_zero, map_zero]
      map_add' := by intro x y; apply hg; rw [hk, map_add, map_add, hk, hk] }
  have hh : Function.Bijective h := by
    constructor
    · intro x y hxy
      apply hf
      rw [← hk x, ← hk y]
      exact congrArg g hxy
    · intro y
      have hy : g y ∈ Set.range f := by rw [hr]; exact ⟨y, rfl⟩
      obtain ⟨x, hxy⟩ := hy
      exact ⟨x, hg ((hk x).trans hxy)⟩
  exact ⟨AddEquiv.ofBijective h hh, hk⟩

private theorem latticeInclusion_injective
    {E : Type} [NormedField E] (A : Subring E) {r : ℕ}
    (N : Submodule A (Fin r → E)) (Z : Type*) [TopologicalSpace Z] :
    Function.Injective (continuousLatticeInclusion A N Z) := by
  intro f g h
  apply ContinuousMap.ext
  intro z
  exact Subtype.ext (ContinuousMap.congr_fun h z)

private theorem presentation_of_range
    {E : Type} [NormedField E] (A : Subring E) [TotallyDisconnectedSpace A]
    (Y : Scheme.{u}) {r : ℕ} (N : Submodule A (Fin r → E))
    {Q R : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) Y)}
    (i : Q ⟶ R) [Mono i]
    (c : ContinuousFunctionPresentation Y A (Fin r → E) R)
    (hr : ∀ B : Y.ProEt,
      Set.range (fun x ↦ c.sections B
        (((continuousRingModuleEquivalence Y A).functor.map i).val.app (op B) x)) =
        Set.range (continuousLatticeInclusion A N B.left)) :
    Nonempty (ContinuousFunctionPresentation Y A N Q) := by
  classical
  let F := (continuousRingModuleEquivalence Y A).functor
  let f := F.map i
  have : Mono f := by dsimp [f]; infer_instance
  have : Mono f.val := inferInstanceAs (Mono ((SheafOfModules.forget _).map f))
  have h (B : Y.ProEt) :
      ∃ e : (F.obj Q).val.obj (op B) ≃+ C(B.left, N),
        ∀ x, continuousLatticeInclusion A N B.left (e x) =
          c.sections B (f.val.app (op B) x) := by
    let a := (c.sections B).toAddMonoidHom.comp (f.val.app (op B)).hom.toAddMonoidHom
    exact additive_equiv_of_equal_ranges a
      (continuousLatticeInclusion A N B.left).toAddMonoidHom
      ((c.sections B).injective.comp (PresheafOfModules.injective_of_mono f.val (op B)))
      (latticeInclusion_injective A N B.left) (hr B)
  choose e he using h
  refine ⟨{ sections := e, restrict := ?_, smul := ?_ }⟩
  · intro B D a x
    apply latticeInclusion_injective A N D.left
    rw [he]
    change c.sections D (f.val.app (op D) ((F.obj Q).val.map a.op x)) =
      (continuousLatticeInclusion A N B.left (e B x)).comp a.left.base.hom
    rw [he, ← c.restrict B D a (f.val.app (op B) x)]
    exact congrArg (c.sections D) (PresheafOfModules.naturality_apply f.val a.op x)
  · intro B a x
    apply latticeInclusion_injective A N B.left
    rw [he]
    change c.sections B (f.val.app (op B) (a • x)) =
      a.down • continuousLatticeInclusion A N B.left (e B x)
    rw [(f.val.app (op B)).hom.map_smul, c.smul, he]

/-- The integral trace image has actual continuous-function charts for finite sums
of full algebraic lattices. This is a chart computation, without a freeness assertion.
Source: blueprint, stratified lattice proof, "Pushing down by the trace";
Bhatt--Scholze, Section 6.8.
(blueprint: lem-sfb-continuous-finite-etale-trace-image-charts)

Proof. Split p over etale neighbourhoods and trivialize P further pro-etale locally.
Use the continuous module encoding, its restriction comparison and its scalar
extension comparison to regard the sheet restrictions of M as embedded integral
lattice pairs in the fixed free rational module. These embeddings are monic:
locally M is finite free, so its scalar-extension unit is a finite sum of the
injective inclusion of continuous integral scalar functions into rational ones;
compose with e and descend monicity. The lattice-class sheaf theorem
identifies their classes with sections of the constant lattice-coset sheaf. There
are finitely many sheets, so choose a common covering refinement on which all
these sections come from fixed algebraic full lattices. Its normalized class
presentation identifies their actual embedded images on every further slice;
equality of their abstract isomorphism classes alone would not suffice.
Surjectivity makes the sheet set nonempty on every nonempty chart. The sheet-sum
formula for the supplied trace identifies its integral image with the sheaf sum
of these embedded sheet lattices, by finite_etale_trace_image. Exact inverse
image and the coefficient equivalences preserve the categorical image. The
continuous lattice sum theorem identifies the sheaf sum with continuous functions
into the algebraic sum: its continuous linear section lifts every function to a
tuple of sheet functions. Thus the sectionwise equivalences are additive,
restriction-compatible, and respect the actual continuous scalar action, as
required by ContinuousFunctionPresentation. Transport the coefficient subring
from Padic.coefficientExtensionIntegers to continuousIntegers using their proved
equality. Bind all refinements to obtain the displayed scheme cover. Empty
members may be discarded; if X is empty use the empty cover. Rank zero uses
zero lattices with their empty bases and the same formulas. -/
theorem continuousFiniteEtaleTrace_image_charts
    (l : ℕ) [Fact l.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [TotallyDisconnectedSpace E] (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hP : LocallyFree (condensedRingObj (Profinite.continuousMapRingObj E) X) P)
    {U : Scheme.{u}} (p : U ⟶ X) [IsFinite p] [Etale p] [Surjective p]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (integralCoeff l E) U))
    (hM : LocallyFree (condensedRingObj (integralCoeff l E) U) M)
    (e : (Mod.extendScalars (coefficientMap (integralScalarMap l E) U)).obj M ≅
      (upperStar (Profinite.continuousMapRingObj E) p).obj P)
    (τ : (lowerStar (Profinite.continuousMapRingObj E) p).obj
      ((upperStar (Profinite.continuousMapRingObj E) p).obj P) ⟶ P)
    (hτ : FiniteEtaleTraceFormula (Profinite.continuousMapRingObj E) p P τ) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
      ∃ (r d : ℕ) (_ : 0 < d)
        (L : Fin d → Submodule (continuousIntegers l E) (Fin r → E)),
        (∀ j, ∃ b : Module.Basis (Fin r) (continuousIntegers l E) (L j),
          ∃ c : Module.Basis (Fin r) E (Fin r → E), ∀ i, (b i : Fin r → E) = c i) ∧
        Nonempty (ContinuousFunctionPresentation (C.X s) (continuousIntegers l E)
          ↥(⨆ j, L j)
          ((upperStar (integralCoeff l E) (C.f s)).obj
            (image (latticePushedEmbedding (integralScalarMap l E) X P p M e ≫
              (Mod.comap (coefficientMap (integralScalarMap l E) X)).map τ)))) := by
  classical
  obtain ⟨C, hC⟩ := continuousFiniteEtaleLattice_sheet_charts l E X P hP p M hM e
  refine ⟨C, fun s ↦ ?_⟩
  obtain ⟨r, d, hd, t, w, hs, L, hL, c, hc⟩ := hC s
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  let : WeaklyEtale (C.f s) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ C.mem₀ (.mk s)
  refine ⟨r, d, hd, L, hL, ?_⟩
  apply presentation_of_range (continuousIntegers l E) (C.X s) (⨆ j, L j)
    (finiteEtaleTraceImageEmbedding (integralScalarMap l E) P p M e τ (C.f s)) c
  intro B
  rw [finiteEtaleTrace_sheet_ranges l E P p M e τ hτ (C.f s) r d hd t w hs L hL c hc B]
  have hsum :
      (⨆ j, (continuousLatticeInclusion (continuousIntegers l E) (L j) B.left).range) =
        (continuousLatticeInclusion (continuousIntegers l E) (⨆ j, L j) B.left).range := by
    have h := (continuous_lattice_sum.{u, 0, 0, u} l E r (Fin d))
    rw [← continuousIntegers_eq l E] at h
    exact (h L hL).2.2 (C.X s) |>.2.2.1 B
  rw [hsum]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
