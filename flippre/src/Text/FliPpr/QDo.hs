-- | Module supposed to be used with @QualifiedDo@.
-- This module re-exports 'mfix' from 'Text.FliPpr.Mfix`, and 'return', '(>>)', '(>>=)', and 'fail' from 'Prelude'.
module Text.FliPpr.QDo (
  mfix,
  return,
  (>>),
  (>>=),
  fail,
)
where

import Text.FliPpr.Mfix (mfix)
import Prelude (fail, return, (>>), (>>=))