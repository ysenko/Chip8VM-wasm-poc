#[cfg(not(test))]
use js_sys::Math::random;

#[cfg(test)]
fn random() -> f64 {
    0.000066
}

pub fn set_panic_hook() {
    // When the `console_error_panic_hook` feature is enabled, we can call the
    // `set_panic_hook` function at least once during initialization, and then
    // we will get better error messages if our code ever panics.
    //
    // For more details see
    // https://github.com/rustwasm/console_error_panic_hook#readme
    #[cfg(feature = "console_error_panic_hook")]
    console_error_panic_hook::set_once();
}

pub fn generate_random_u8() -> u8 {
    (((random() * 1000000.0) as u32) % 255) as u8
}

pub fn get_pixel_idx(row: usize, col: usize, width: usize, height: usize) -> usize {
    (row % height) * width + (col % width)
}

#[cfg(test)]
mod tests {
    use super::{generate_random_u8, get_pixel_idx};

    #[test]
    fn test_generate_random_u8() {
        assert_eq!(0x42, generate_random_u8());
    }

    #[test]
    fn test_get_pixel_idx() {
        let cases: Vec<(usize, usize, usize, usize, usize)> = vec![
            // col, row, width, height, expected_idx
            (0, 0, 128, 64, 0),
            (127, 63, 128, 64, 8191),
            (128, 64, 128, 64, 0),
            (129, 65, 128, 64, 129),
        ];

        for (col, row, width, height, expected_idx) in cases.into_iter() {
            assert_eq!(expected_idx, get_pixel_idx(row, col, width, height));
        }
    }
}
