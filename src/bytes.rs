use std::{alloc, ptr, slice};
use std::alloc::Layout;
use std::ops::Deref;
use std::ptr::NonNull;


pub(crate) struct RawBytes {
    pub(crate) cap: usize,
    pub(crate) bytes: NonNull<u8>,
    pub(crate) nbytes: usize
}

impl RawBytes {
    pub fn as_ptr_const(&self) -> *const u8 { self.bytes.as_ptr().cast_const() }

    pub fn as_ptr_mut(&self) -> *mut u8 { self.bytes.as_ptr() }

    pub fn expand_to(&mut self, nbytes: usize) {
        let new_layout = Layout::array::<u8>(nbytes).unwrap();

        assert!(new_layout.size() <= isize::MAX as usize, "Allocation too large");

        let pointer = if self.cap == 0 {
            unsafe { alloc::alloc(new_layout) }
        } else {
            let old_layout = Layout::array::<u8>(self.cap).unwrap();
            let old_pointer = self.bytes.as_ptr();

            unsafe { alloc::realloc(old_pointer, old_layout, new_layout.size()) }
        };

        self.bytes = match NonNull::new(pointer) {
            Some(p) => p,
            None => alloc::handle_alloc_error(new_layout)
        };

        self.cap = nbytes;
    }

    pub fn shift_right(&mut self, end: usize, mask: u8, up: usize, down: usize) {
        unsafe {
            let pointer = self.bytes.as_ptr();

            for i in 0..(end - 1) {
                *pointer.add(i) >>= down;
                *pointer.add(i) |= (*pointer.add(i + 1) & mask) << up;
            }

            *pointer.add(end - 1) >>= down;
        }
    }

    pub fn shift_right_from(&mut self, start: usize, end: usize, mask: u8, up: usize, down: usize) {
        unsafe {
            let pointer = self.bytes.as_ptr();

            for i in start..end {
                *pointer.add(i - 1) |= (*pointer.add(i) & mask) << up;
                *pointer.add(i) >>= down;
            }
        }
    }

    pub fn shrink_to(&mut self, nbytes: usize) {
        if self.cap <= nbytes { return; }

        let old_layout = Layout::array::<u8>(self.cap).unwrap();
        let old_pointer = self.bytes.as_ptr();

        unsafe {
            for i in nbytes..self.nbytes { ptr::read(old_pointer.add(i)); }

            if nbytes == 0 {
                alloc::dealloc(old_pointer, old_layout);
                self.bytes = NonNull::dangling();
            } else {
                let new_layout = Layout::array::<u8>(nbytes).unwrap();
                let pointer = alloc::realloc(old_pointer, old_layout, new_layout.size());

                self.bytes = match NonNull::new(pointer) {
                    Some(p) => p,
                    None => alloc::handle_alloc_error(new_layout)
                };
            }
        }

        self.cap = nbytes;
        self.nbytes = nbytes;
    }
}

impl Deref for RawBytes {
    type Target = [u8];

    fn deref(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.as_ptr_const(), self.nbytes) }
    }
}

impl Drop for RawBytes {
    fn drop(&mut self) {

        if self.cap != 0 {
            unsafe {
                alloc::dealloc(self.bytes.as_ptr(), Layout::array::<u8>(self.cap).unwrap());
            }
        }
    }
}

unsafe impl Send for RawBytes {}

unsafe impl Sync for RawBytes {}