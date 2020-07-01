{-# LANGUAGE GADTs #-}

module Dim.Dim where

import           Prelude
-- import           Debug.Trace

import           Data.Vector.Storable           ( Vector )


data Column a = Column !(Vector a)

