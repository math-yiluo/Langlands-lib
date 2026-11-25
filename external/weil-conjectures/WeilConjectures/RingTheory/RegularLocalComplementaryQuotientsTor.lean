/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Length
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Single
import WeilConjectures.RingTheory.RegularLocalComplementaryKoszulData
import WeilConjectures.RingTheory.RegularLocalComplementaryTorLengthData

/-!
# Tor for complementary regular local quotients

Source: Stacks Project, `intersection.tex`, Tag 0B1I, proof of
`intersection-lemma-transversal`.
(blueprint: lem-trf-regular-local-complementary-quotients-tor)

The Koszul augmentations and the degree-zero Tor identification are normalized
by the quotient and residue maps. Empty parameter prefixes are permitted.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

namespace RingTheory

/-- Complementary regular local quotients meeting in the residue field have no higher Tor;
their Koszul resolution remains acyclic in positive degrees after tensoring.
Source: Stacks Project, `intersection.tex`, Tag 0B1I, proof of
`intersection-lemma-transversal`.
(blueprint: lem-trf-regular-local-complementary-quotients-tor)

Proof:
1. `regularLocal_complementary_koszul_data`
   (`new-d3-regular-local-complementary-koszul-data`) gives the parameters `f`, the
   prefix `g` generating `I`, regularity over `A` and over `A/J`, the finite free
   Koszul terms vanishing above `r`, the normalized quotient augmentation `ε`, positive
   tensor-homology vanishing, the normalized augmentation `δ` and the residue map `e`.
2. `regularLocal_complementary_tor_length_data`
   (`new-d3-regular-local-complementary-tor-length-data`), applied to `g`, the span
   equality, the positive tensor-homology vanishing, the freeness of the Koszul terms
   and the quasi-isomorphism `ε` of step 1, gives positive Tor vanishing, the
   normalized degree-zero tensor and Tor isomorphisms, finite lengths and the
   alternating sum. The conclusion is the conjunction of both lists of clauses.
-/
theorem regularLocal_complementary_quotients_tor
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (r s : ℕ) (hdim : ringKrullDim A = ((r + s : ℕ) : WithBot ℕ∞))
    (I J : Ideal A) (hI : I ≠ ⊤) (hJ : J ≠ ⊤)
    [IsRegularLocalRing (A ⧸ I)] [IsRegularLocalRing (A ⧸ J)]
    (hIdim : ringKrullDim (A ⧸ I) = (s : WithBot ℕ∞))
    (hJdim : ringKrullDim (A ⧸ J) = (r : WithBot ℕ∞))
    (htrans : I ⊔ J = IsLocalRing.maximalIdeal A) :
    ∃ (f : Fin (r + s) → A) (g : Fin r → A),
      g = (fun i ↦ f (Fin.castAdd s i)) ∧
      IsLocalRing.IsRegularSystemOfParameters (List.ofFn f) ∧
      I = Ideal.span (Set.range g) ∧
      RingTheory.Sequence.IsRegular A (List.ofFn g) ∧
      RingTheory.Sequence.IsRegular (A ⧸ J)
        (List.ofFn (fun i ↦ Ideal.Quotient.mk J (g i))) ∧
      (∀ n : ℕ, Module.Free A ((ExteriorAlgebra.koszulComplex A r g).X n) ∧
        Module.Finite A ((ExteriorAlgebra.koszulComplex A r g).X n)) ∧
      (∀ n : ℕ, r < n → IsZero ((ExteriorAlgebra.koszulComplex A r g).X n)) ∧
      (∃ ε : ExteriorAlgebra.koszulComplex A r g ⟶
          (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A (A ⧸ I)),
        QuasiIso ε ∧ ∀ x : ⋀[A]^0 (Fin r →₀ A),
          ε.f 0 x = Ideal.Quotient.mk I (exteriorPower.zeroEquiv A (Fin r →₀ A) x)) ∧
      (∀ n : ℕ, 0 < n →
        IsZero ((ExteriorAlgebra.koszulComplexTensor A r g (A ⧸ J)).homology n)) ∧
      (∃ δ : ExteriorAlgebra.koszulComplexTensor A r g (A ⧸ J) ⟶
          (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A (A ⧸ (I ⊔ J))),
        QuasiIso δ ∧ ∀ (x : ⋀[A]^0 (Fin r →₀ A)) (a : A),
          δ.f 0 (x ⊗ₜ[A] Ideal.Quotient.mk J a) =
            Ideal.Quotient.mk (I ⊔ J) (exteriorPower.zeroEquiv A (Fin r →₀ A) x * a)) ∧
      (∃ e : ModuleCat.of A (A ⧸ (I ⊔ J)) ≅
          ModuleCat.of A (IsLocalRing.ResidueField A),
        ∀ a : A, e.hom (Ideal.Quotient.mk (I ⊔ J) a) = IsLocalRing.residue A a) ∧
      (∀ i : ℕ, 0 < i →
        IsZero (((Tor' (ModuleCat.{u} A) i).obj (ModuleCat.of A (A ⧸ I))).obj
          (ModuleCat.of A (A ⧸ J)))) ∧
      (∃ eTensor : ModuleCat.of A ((A ⧸ I) ⊗[A] (A ⧸ J)) ≅
          ModuleCat.of A (IsLocalRing.ResidueField A),
        ∃ eTor : (((Tor' (ModuleCat.{u} A) 0).obj (ModuleCat.of A (A ⧸ I))).obj
            (ModuleCat.of A (A ⧸ J))) ≅ ModuleCat.of A (IsLocalRing.ResidueField A),
          (∀ a b : A, eTensor.hom
            (Ideal.Quotient.mk I a ⊗ₜ[A] Ideal.Quotient.mk J b) =
              IsLocalRing.residue A (a * b)) ∧
          eTor.hom = (Functor.fromLeftDerivedZero
            ((tensoringRight (ModuleCat.{u} A)).obj (ModuleCat.of A (A ⧸ J)))).app
              (ModuleCat.of A (A ⧸ I)) ≫ eTensor.hom) ∧
      (∀ i : ℕ, Module.length A
        (((Tor' (ModuleCat.{u} A) i).obj (ModuleCat.of A (A ⧸ I))).obj
          (ModuleCat.of A (A ⧸ J))) ≠ ⊤) ∧
      (∑ i ∈ Finset.range (r + 1), (-1 : ℤ) ^ i *
        (Module.length A
          (((Tor' (ModuleCat.{u} A) i).obj (ModuleCat.of A (A ⧸ I))).obj
            (ModuleCat.of A (A ⧸ J)))).toNat) = 1 := by
  obtain ⟨f, g, hfg, hf, hIspan, hregA, hregB, hterms, hzero, hε, hpos,
      hδ, he⟩ := regularLocal_complementary_koszul_data A r s hdim I J hI hJ
      hIdim hJdim htrans
  obtain ⟨htor, ⟨eTensor, eTor, hetensor, hetor⟩, hlen, hsum⟩ :=
    regularLocal_complementary_tor_length_data A r I J g hIspan hpos
      (fun n ↦ (hterms n).1) (by
        obtain ⟨ε, hεq, _⟩ := hε
        exact ⟨ε, hεq⟩) htrans
  exact ⟨f, g, hfg, hf, hIspan, hregA, hregB, hterms, hzero, hε, hpos,
    hδ, he, htor, ⟨eTensor, eTor, hetensor, hetor⟩, hlen, hsum⟩

end RingTheory
