/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.Abelian
public import WeilConjectures.Topology.AbelianOpenExtensionByZero
import WeilConjectures.Topology.AbelianOpenExtensionByZeroStalks
import WeilConjectures.Topology.ConstantSheafLocallyConstantComparison
import WeilConjectures.Topology.PresheafModuleStalkFunctor
import WeilConjectures.Topology.ConstantSubsheafNormalizedCore

/-! # ConstantSubsheafNormalizedPresentation

Source: Stacks Project, Cohomology, Lemma 0A38
(blueprint: lem-sc-constant-subsheaf-normalized-presentation).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

/-- Source: Stacks Project, Cohomology, Lemma 0A38.
Proof: Normalize the generating sections using the constant-sheaf identification isoC.
Each locally constant section on a compact open has finitely many clopen fibres; these
fibres are compact in X. Restrict to the fibres, delete zero values, and negate sections
with negative value. Adjoin the intersections of all nonempty subsets and their positive
gcd sections. Bezout gives these sections in K. Binary compact-intersection closure
makes all these opens compact. At every point the gcd of its active labels is attained,
and the sections generate the same stalk subgroup as the original epimorphism. Stalk
coordinates for isoC and the supplied e differ by an automorphism of the integers,
hence by sign, so this gcd is at most b+1. Retain only labels at most b+1: an attained
gcd remains at every nonzero stalk. Thus the retained coproduct map is epi and still has
the attained-divisor property. Its sections are the images of the canonical unit 1,
which gives hsection, and their positive constant values give hvalue. Empty families
are allowed, and give n=0.
(blueprint: lem-sc-constant-subsheaf-normalized-presentation). -/
theorem constantSubsheaf_normalized_presentation
    (X : TopCat.{u}) (K C : Sheaf AddCommGrpCat X) (ι : K ⟶ C) [Mono ι]
    (isoC : C ≅ (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))
    (hqc : ∀ U V : Opens X, IsCompact (U : Set X) → IsCompact (V : Set X) →
      IsCompact ((U ⊓ V : Opens X) : Set X))
    (hgen : ∃ (n : ℕ) (U : Fin n → Opens X)
      (_ : ∀ i, IsCompact ((U i : Opens X) : Set X)),
      ∃ g : (∐ fun i => (abelianOpenExtensionByZero (U i)).obj
        ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ K, Epi g)
    (e : ∀ x : X, TopCat.Presheaf.stalk C.obj x ≅ AddCommGrpCat.of (ULift.{u} ℤ))
    (b : ℕ)
    (hb : ∀ x : X, ∃ a : ℕ, a ≤ b + 1 ∧
      Set.range (fun t : ToType (TopCat.Presheaf.stalk K.obj x) ↦
        (e x).hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ι.hom t)) =
      Set.range (fun z : ULift.{u} ℤ ↦ (a : ℤ) • z)) :
    ∃ (n : ℕ) (A : Fin n → Opens X) (_ : ∀ i, IsCompact (A i : Set X))
      (c : Fin n → ℕ), (∀ i, 0 < c i ∧ c i ≤ b + 1) ∧
      ∃ (g : (∐ fun i => (abelianOpenExtensionByZero (A i)).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ K), Epi g ∧
        ∃ s : ∀ i, K.obj.obj (op (A i)),
          ( ∀ i,
      (Sigma.ι (fun j => (abelianOpenExtensionByZero (A j)).obj
        ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A j)))
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) i ≫ g).hom.app
        (op (A i))
        (abelianOpenExtensionSection (A i)
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) (A i) le_rfl
          ((toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
            ((Functor.const (Opens ((Opens.toTopCat X).obj (A i)))ᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u} ℤ)))).app
            (op ((Opens.map (A i).inclusion').obj (A i))) (ULift.up 1))) = s i) ∧
          ( ∀ i, (ι ≫ isoC.hom).hom.app (op (A i)) (s i) =
      (toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))).app
          (op (A i)) (ULift.up (c i : ℤ))) ∧
          (∀ x : X, x ∈ iSup A →
            ∃ i, x ∈ A i ∧ ∀ j, x ∈ A j → c i ∣ c j) := by
  obtain ⟨d, _⟩ := constantSubsheaf_normalized_core X K C ι isoC hqc hgen e b hb
  exact constantSubsheaf_normalized_completion X K C ι isoC hqc hgen e b hb d

end TopCat.Sheaf
