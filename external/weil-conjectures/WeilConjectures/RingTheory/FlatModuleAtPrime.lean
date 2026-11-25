/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness

/-!
# Flat modules localized at a prime of an algebra

Source: Stacks Project, Algebra, Lemma 10.39.18 (Tag 00HT), part (6), only-if direction
(blueprint: lem-pc-affine-flat-module-local-criterion).
-/

@[expose] public section

namespace Module.Flat

/-- Stacks Project, Algebra, Lemma 10.39.18 (Tag 00HT), part (6), only-if direction
(blueprint: lem-pc-affine-flat-module-local-criterion). Fix `q` and contract it to `p` in `R`.
Localizing the `A`-module `M` away from `q` preserves its flatness over `R` by
`lem-pc-affine-flat-module-localization-preserves-flatness`. Every element outside `p`
maps to a unit in `A_q`, giving `M_q` its `R_p`-module structure. Finally,
`lem-weil-pbc-flat-over-localization` identifies flatness of this module over `R` with
flatness over `R_p`. -/
theorem localizedModule_atPrime_of_flat {R A M : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommMonoid M] [Module A M] (q : Ideal A) [q.IsPrime]
    (hflat : @Module.Flat R M _ _ (Module.compHom M (algebraMap R A))) :
    @Module.Flat (Localization.AtPrime (q.comap (algebraMap R A)))
      (LocalizedModule q.primeCompl M) _ _
      (Module.compHom _ (Localization.localRingHom (q.comap (algebraMap R A)) q
        (algebraMap R A) rfl)) := by
  let : Module R M := Module.compHom M (algebraMap R A)
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup A
  have : IsScalarTower R A M := IsScalarTower.of_compHom R A M
  let p := q.comap (algebraMap R A)
  let Rp := Localization.AtPrime p
  let Mq := LocalizedModule q.primeCompl M
  let : Module Rp Mq := Module.compHom Mq
    (Localization.localRingHom p q (algebraMap R A) rfl)
  have hloc : Module.Flat R Mq := localizedModule_of_algebra q.primeCompl hflat
  have : IsScalarTower R Rp Mq := by
    constructor
    intro r s m
    change Localization.localRingHom p q (algebraMap R A) rfl (r • s) • m =
      r • (Localization.localRingHom p q (algebraMap R A) rfl s • m)
    rw [Algebra.smul_def, map_mul, Localization.localRingHom_to_map, mul_smul]
    rw [IsScalarTower.algebraMap_smul (R := A) (A := Localization.AtPrime q)]
    rw [IsScalarTower.algebraMap_smul (R := R) (A := A)]
  exact (Module.flat_iff_of_isLocalization Rp p.primeCompl Mq).mpr hloc

end Module.Flat
