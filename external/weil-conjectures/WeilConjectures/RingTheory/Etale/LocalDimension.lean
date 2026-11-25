/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Unramified.LocalStructure
import WeilConjectures.RingTheory.QuasiFiniteLocalDimension
import WeilConjectures.RingTheory.RingKrullDimLeOfFaithfullyFlatOfIsLocalHom

/-!
# Local dimension under an étale ring map

Source: Stacks Project, More on Algebra, Lemma Tag 07QP
(blueprint: lem-sc-etale-local-dimension).
-/

@[expose] public section

universe u v

namespace RingHom.Etale

/-- Localizing an étale ring map at a prime and its contraction preserves Krull dimension.
Source: Stacks Project, More on Algebra, Lemma Tag 07QP
(blueprint: lem-sc-etale-local-dimension).

Proof: The induced map on localizations is flat and local
(`lem-weil-pbc-etale-algebra-flat`, `lem-weil-pbc-flat-local-ring-maps`), hence faithfully flat
(`lem-pc-local-flat-faithful-flat-reflects-surjective`). Going down yields the lower bound
`dim A_p ≤ dim B_q` (`lem-sc-faithfully-flat-local-dimension`).
For the reverse bound, the étale map is of finite type and quasi-finite at `q`
(Mathlib gives finite type and discrete fibre spectra). Apply the local dimension inequality
(`lem-weil-pbc-dimension-inequality-quasi-finite`) to obtain `dim B_q ≤ dim A_p`.
Antisymmetry gives the asserted equality. -/
theorem ringKrullDim_localization_eq {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Etale) (q : Ideal B) [q.IsPrime] :
    ringKrullDim (Localization.AtPrime (Ideal.comap f q)) =
      ringKrullDim (Localization.AtPrime q) := by
  let := f.toAlgebra
  have : Algebra.Etale A B := hf
  apply le_antisymm
  · let g := Localization.localRingHom (Ideal.comap f q) q f rfl
    have hg : g.Flat := (Etale.iff_flat_and_formallyUnramified.mp hf).1.localRingHom
      q (Ideal.comap f q) rfl
    let := g.toAlgebra
    have : IsLocalHom (algebraMap (Localization.AtPrime (Ideal.comap f q))
        (Localization.AtPrime q)) := show IsLocalHom g from inferInstance
    have : Module.Flat (Localization.AtPrime (Ideal.comap f q))
        (Localization.AtPrime q) := hg
    have hgfaithful : g.FaithfullyFlat :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact RingHom.ringKrullDim_le_of_faithfullyFlat_of_isLocalHom g hgfaithful
  · have hq : Algebra.IsQuasiFiniteAtPrime A B ⟨q, inferInstance⟩ := by
      unfold Algebra.IsQuasiFiniteAtPrime
      exact isOpen_discrete _
    exact Algebra.ringKrullDim_le_of_isQuasiFiniteAtPrime A B ⟨q, inferInstance⟩ hq

end RingHom.Etale
