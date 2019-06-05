// MD5 implementation based on RFC.

static
UINT32
GetUINT32LittleEndian(__in_bcount(4) const UINT8* a)
{
#if defined(_X86_) || defined(_AMD64_)
    return *(const UINT32*)a;
#else
    return ((UINT32)a[0]) | (((UINT32)a[1]) << 8) | (((UINT32)a[2]) << 16) | (((UINT32)a[3]) << 24);
#endif
}

static
UINT32
GetUINT32BigEndian(__in_bcount(4) const UINT8* a)
{
#if (defined(_X86_) || defined(_AMD64_)) && (_MSC_VER >= 1400)
    return _byteswap_ulong(*(const UINT32*)a);
#else
    return ((UINT32)a[3]) | (((UINT32)a[2]) << 8) | (((UINT32)a[1]) << 16) | (((UINT32)a[0]) << 24);
#endif
}

static
void
PutUINT32LittleEndian(__out_bcount(4) void* v,
                      __in UINT32 b)
{
#if defined(_X86_) || defined(_AMD64_)
    *(UINT32*)v = b;
#else
    UINT8 * const a = (UINT8*)v;
    a[0] = (UINT8)b;
    a[1] = (UINT8)(b >> 8);
    a[2] = (UINT8)(b >> 16);
    a[3] = (UINT8)(b >> 24);
#endif
}

static
void
PutUINT64LittleEndian(_Out_writes_all_(8) void* v,
                      __in UINT64 b)
{
#if defined(_X86_) || defined(_AMD64_)
    *(UINT64*)v = b;
#else
    UINT8 * const a = (UINT8*)v;
    a[0] = (UINT8)b;
    a[1] = (UINT8)(b >> 8);
    a[2] = (UINT8)(b >> 16);
    a[3] = (UINT8)(b >> 24);
    a[4] = (UINT8)(b >> 32);
    a[5] = (UINT8)(b >> 40);
    a[6] = (UINT8)(b >> 48);
    a[7] = (UINT8)(b >> 56);
#endif
}

static
void
PutUINT64BigEndian(_Out_writes_all_(8) void* v,
                   __in UINT64 b)
{
#if (defined(_X86_) || defined(_AMD64_)) && (_MSC_VER >= 1400)
    *(UINT64*)v = _byteswap_uint64(b);
#else
    UINT8 * const a = (UINT8*)v;
    a[7] = (UINT8)b;
    a[6] = (UINT8)(b >> 8);
    a[5] = (UINT8)(b >> 16);
    a[4] = (UINT8)(b >> 24);
    a[3] = (UINT8)(b >> 32);
    a[2] = (UINT8)(b >> 40);
    a[1] = (UINT8)(b >> 48);
    a[0] = (UINT8)(b >> 56);
#endif
}

void
ComputeMD5(__in_bcount(Length) const void* VoidData,
           __in size_t Length,
           __out UINT8 Hash[MD5DIGESTLEN])
{
    const UINT8* Data = (const UINT8*)VoidData;
    UINT32 h0 = 0x67452301;
    UINT32 h1 = 0xEFCDAB89;
    UINT32 h2 = 0x98BADCFE;
    UINT32 h3 = 0x10325476;
    UINT chunkCount = 0;
    UINT chunk = 0;
    UINT32 f = 0;
    UINT32 t = 0;
    struct {
        const UINT8* Data;
        size_t BlockCount; // 64 bytes each
    } chunks[3] = { 0 };
    UINT8 Tail[128] = { 0 };
/*
Algorithm includes:
    append 0x80
    append some zeros
    append the size in bits mod 2^64 as a 64bit little endian integer
    The number of zeros appended is such that the overall size is a multiple of 64.
    Do a bunch of math, operating on 64byte chunks.

"Tail" is the chunk of data at the end with 0x80, zeros, and the length.
It is back-filled with data from the end of data to be a multiple of 64 bytes in length.

data[x:y] is y bytes of data starting at offset x; y can be 0
0[x] is x zero; x can be zero
! delimits 64-byte chunks -- there can be two tails if Length / 64 < (Length + 9) / 64
aka (64 - Length % 64) < 9

"Tail" correlates to "writable buffer" and "copy".

We "never" copy the input data, except as needed to form a buffer that
is a multiple of 64 bytes in length.

The formulas/patterns can be seen by studying examples.

    0  bytes => tail is data[0:0] 0x80 0[55] 0 0[7]
    1  bytes => tail is data[0:1] 0x80 0[54] 1 0[7]
    2  bytes => tail is data[0:2] 0x80 0[53] 2 0[7]
    ..
    54  bytes => tail is data[0:54] 0x80 0[1] 54 0[7]
    55  bytes => tail is data[0:55] 0x80 0[0] 55 0[7]
    56  bytes => tail is data[0:56] 0x80 0[7] ! 0[56] 56 0[7]
    57  bytes => tail is data[0:57] 0x80 0[6] ! 0[56] 57 0[7]
    58  bytes => tail is data[0:58] 0x80 0[5] ! 0[56] 58 0[7]
    59  bytes => tail is data[0:59] 0x80 0[4] ! 0[56] 59 0[7]
    60  bytes => tail is data[0:60] 0x80 0[3] ! 0[56] 60 0[7]
    61  bytes => tail is data[0:61] 0x80 0[2] | 0[56] 61 0[7]
    62  bytes => tail is data[0:62] 0x80 0[1] ! 0[56] 62 0[7]
    63  bytes => tail is data[0:63] 0x80 0[0] ! 0[56] 63 0[7]
    64  bytes => tail is data[64:0] 0x80 0[55] 64 0[7]
    65  bytes => tail is data[64:1] 0x80 0[54] 65 0[7]
    66  bytes => tail is data[64:2] 0x80 0[53] 66 0[7]
    ..
    119 bytes => tail is data[64:55] 0x80 119 0[7]
    120 bytes => tail is data[64:56] 0x80 0[7] ! 0[56] 123 0[7]
    121 bytes => tail is data[64:57] 0x80 0[6] ! 0[56] 123 0[7]
    122 bytes => tail is data[64:58] 0x80 0[5] ! 0[56] 123 0[7]
    123 bytes => tail is data[64:59] 0x80 0[4] ! 0[56] 123 0[7]
    124 bytes => tail is data[64:60] 0x80 0[3] ! 0[56] 124 0[7]
    125 bytes => tail is data[64:61] 0x80 0[2] ! 0[56] 125 0[7]
    126 bytes => tail is data[64:62] 0x80 0[1] ! 0[56] 126 0[7]
    127 bytes => tail is data[64:63] 0x80 0[0] ! 0[56] 127 0[7]
    128 bytes => tail is data[128:0] 0x80 0[55] 128 0[7]
    129 bytes => tail is data[128:1] 0x80 0[54] 65 0[7]
*/
    size_t lengthMod64 = (Length ? (Length % 64) : 0);
    size_t room = (64 - lengthMod64);
    size_t zeros = { 0 };
    if (room < 9)
    {
        zeros = 56 + room - 1;
        chunkCount = 3;
    }
    else
    {
        zeros = room - 9;
        chunkCount = 2;
    }
    CopyMemory(&Tail[0], &Data[Length - lengthMod64], lengthMod64);
    Tail[lengthMod64] = 0x80;
    PutUINT64LittleEndian(&Tail[lengthMod64 + zeros + 1], Length * 8);
    chunks[0].Data = Data;
    chunks[0].BlockCount = Length / 64;
    chunks[1].Data = Tail;
    chunks[1].BlockCount = 1;
    chunks[2].Data = &Tail[64];
    chunks[2].BlockCount = 1;

    for (chunk = 0; chunk < chunkCount; ++chunk)
    {
        size_t const blockCount = chunks[chunk].BlockCount;
        UINT8 const * const chunkData = chunks[chunk].Data;
        size_t block = { 0 };
        for (block = 0; block < blockCount; ++block)
        {
            UINT32 a = h0;
            UINT32 b = h1;
            UINT32 c = h2;
            UINT32 d = h3;
            UINT8 const * const B = &chunkData[block * 64];
            UINT32 const b0 = GetUINT32LittleEndian(B + 0 * 4);
            UINT32 const b1 = GetUINT32LittleEndian(B + 1 * 4);
            UINT32 const b2 = GetUINT32LittleEndian(B + 2 * 4);
            UINT32 const b3 = GetUINT32LittleEndian(B + 3 * 4);
            UINT32 const b4 = GetUINT32LittleEndian(B + 4 * 4);
            UINT32 const b5 = GetUINT32LittleEndian(B + 5 * 4);
            UINT32 const b6 = GetUINT32LittleEndian(B + 6 * 4);
            UINT32 const b7 = GetUINT32LittleEndian(B + 7 * 4);
            UINT32 const b8 = GetUINT32LittleEndian(B + 8 * 4);
            UINT32 const b9 = GetUINT32LittleEndian(B + 9 * 4);
            UINT32 const b10 = GetUINT32LittleEndian(B + 10 * 4);
            UINT32 const b11 = GetUINT32LittleEndian(B + 11 * 4);
            UINT32 const b12 = GetUINT32LittleEndian(B + 12 * 4);
            UINT32 const b13 = GetUINT32LittleEndian(B + 13 * 4);
            UINT32 const b14 = GetUINT32LittleEndian(B + 14 * 4);
            UINT32 const b15 = GetUINT32LittleEndian(B + 15 * 4);

            f = (b & c) | (~b & d); t = d; d = c; c = b; b += _lrotl(a + f + 0xD76AA478 + b0,  7); a = t;
            f = (b & c) | (~b & d); t = d; d = c; c = b; b += _lrotl(a + f + 0xE8C7B756 + b1, 12); a = t;
            f = (b & c) | (~b & d); t = d; d = c; c = b; b += _lrotl(a + f + 0x242070DB + b2, 17); a = t;
            f = (b & c) | (~b & d); t = d; d = c; c = b; b += _lrotl(a + f + 0xC1BDCEEE + b3, 22); a = t;
            f = (b & c) | (~b & d); t = d; d = c; c = b; b += _lrotl(a + f + 0xF57C0FAF + b4,  7); a = t;
            f = (b & c) | (~b & d); t = d; d = c; c = b; b += _lrotl(a + f + 0x4787C62A + b5, 12); a = t;
            f = (b & c) | (~b & d); t = d; d = c; c = b; b += _lrotl(a + f + 0xA8304613 + b6, 17); a = t;
            f = (b & c) | (~b & d); t = d; d = c; c = b; b += _lrotl(a + f + 0xFD469501 + b7, 22); a = t;
            f = (b & c) | (~b & d); t = d; d = c; c = b; b += _lrotl(a + f + 0x698098D8 + b8,  7); a = t;
            f = (b & c) | (~b & d); t = d; d = c; c = b; b += _lrotl(a + f + 0x8B44F7AF + b9, 12); a = t;
            f = (b & c) | (~b & d); t = d; d = c; c = b; b += _lrotl(a + f + 0xFFFF5BB1 + b10, 17); a = t;
            f = (b & c) | (~b & d); t = d; d = c; c = b; b += _lrotl(a + f + 0x895CD7BE + b11, 22); a = t;
            f = (b & c) | (~b & d); t = d; d = c; c = b; b += _lrotl(a + f + 0x6B901122 + b12,  7); a = t;
            f = (b & c) | (~b & d); t = d; d = c; c = b; b += _lrotl(a + f + 0xFD987193 + b13, 12); a = t;
            f = (b & c) | (~b & d); t = d; d = c; c = b; b += _lrotl(a + f + 0xA679438E + b14, 17); a = t;
            f = (b & c) | (~b & d); t = d; d = c; c = b; b += _lrotl(a + f + 0x49B40821 + b15, 22); a = t;

            f = (d & b) | (~d & c); t = d; d = c; c = b; b += _lrotl(a + f + 0xF61E2562 + b1,   5); a = t;
            f = (d & b) | (~d & c); t = d; d = c; c = b; b += _lrotl(a + f + 0xC040B340 + b6,   9); a = t;
            f = (d & b) | (~d & c); t = d; d = c; c = b; b += _lrotl(a + f + 0x265E5A51 + b11, 14); a = t;
            f = (d & b) | (~d & c); t = d; d = c; c = b; b += _lrotl(a + f + 0xE9B6C7AA + b0,  20); a = t;
            f = (d & b) | (~d & c); t = d; d = c; c = b; b += _lrotl(a + f + 0xD62F105D + b5,   5); a = t;
            f = (d & b) | (~d & c); t = d; d = c; c = b; b += _lrotl(a + f + 0x02441453 + b10,  9); a = t;
            f = (d & b) | (~d & c); t = d; d = c; c = b; b += _lrotl(a + f + 0xD8A1E681 + b15, 14); a = t;
            f = (d & b) | (~d & c); t = d; d = c; c = b; b += _lrotl(a + f + 0xE7D3FBC8 + b4,  20); a = t;
            f = (d & b) | (~d & c); t = d; d = c; c = b; b += _lrotl(a + f + 0x21E1CDE6 + b9,   5); a = t;
            f = (d & b) | (~d & c); t = d; d = c; c = b; b += _lrotl(a + f + 0xC33707D6 + b14,  9); a = t;
            f = (d & b) | (~d & c); t = d; d = c; c = b; b += _lrotl(a + f + 0xF4D50D87 + b3,  14); a = t;
            f = (d & b) | (~d & c); t = d; d = c; c = b; b += _lrotl(a + f + 0x455A14ED + b8,  20); a = t;
            f = (d & b) | (~d & c); t = d; d = c; c = b; b += _lrotl(a + f + 0xA9E3E905 + b13,  5); a = t;
            f = (d & b) | (~d & c); t = d; d = c; c = b; b += _lrotl(a + f + 0xFCEFA3F8 + b2,   9); a = t;
            f = (d & b) | (~d & c); t = d; d = c; c = b; b += _lrotl(a + f + 0x676F02D9 + b7,  14); a = t;
            f = (d & b) | (~d & c); t = d; d = c; c = b; b += _lrotl(a + f + 0x8D2A4C8A + b12, 20); a = t;

            f = b ^ c ^ d; t = d; d = c; c = b; b += _lrotl(a + f + 0xFFFA3942 + b5,   4); a = t;
            f = b ^ c ^ d; t = d; d = c; c = b; b += _lrotl(a + f + 0x8771F681 + b8,  11); a = t;
            f = b ^ c ^ d; t = d; d = c; c = b; b += _lrotl(a + f + 0x6D9D6122 + b11, 16); a = t;
            f = b ^ c ^ d; t = d; d = c; c = b; b += _lrotl(a + f + 0xFDE5380C + b14, 23); a = t;
            f = b ^ c ^ d; t = d; d = c; c = b; b += _lrotl(a + f + 0xA4BEEA44 + b1,   4); a = t;
            f = b ^ c ^ d; t = d; d = c; c = b; b += _lrotl(a + f + 0x4BDECFA9 + b4,  11); a = t;
            f = b ^ c ^ d; t = d; d = c; c = b; b += _lrotl(a + f + 0xF6BB4B60 + b7,  16); a = t;
            f = b ^ c ^ d; t = d; d = c; c = b; b += _lrotl(a + f + 0xBEBFBC70 + b10, 23); a = t;
            f = b ^ c ^ d; t = d; d = c; c = b; b += _lrotl(a + f + 0x289B7EC6 + b13,  4); a = t;
            f = b ^ c ^ d; t = d; d = c; c = b; b += _lrotl(a + f + 0xEAA127FA + b0,  11); a = t;
            f = b ^ c ^ d; t = d; d = c; c = b; b += _lrotl(a + f + 0xD4EF3085 + b3,  16); a = t;
            f = b ^ c ^ d; t = d; d = c; c = b; b += _lrotl(a + f + 0x04881D05 + b6,  23); a = t;
            f = b ^ c ^ d; t = d; d = c; c = b; b += _lrotl(a + f + 0xD9D4D039 + b9,   4); a = t;
            f = b ^ c ^ d; t = d; d = c; c = b; b += _lrotl(a + f + 0xE6DB99E5 + b12, 11); a = t;
            f = b ^ c ^ d; t = d; d = c; c = b; b += _lrotl(a + f + 0x1FA27CF8 + b15, 16); a = t;
            f = b ^ c ^ d; t = d; d = c; c = b; b += _lrotl(a + f + 0xC4AC5665 + b2,  23); a = t;

            f = c ^ (b | ~d); t = d; d = c; c = b; b += _lrotl(a + f + 0xF4292244 + b0,   6); a = t;
            f = c ^ (b | ~d); t = d; d = c; c = b; b += _lrotl(a + f + 0x432AFF97 + b7,  10); a = t;
            f = c ^ (b | ~d); t = d; d = c; c = b; b += _lrotl(a + f + 0xAB9423A7 + b14, 15); a = t;
            f = c ^ (b | ~d); t = d; d = c; c = b; b += _lrotl(a + f + 0xFC93A039 + b5,  21); a = t;
            f = c ^ (b | ~d); t = d; d = c; c = b; b += _lrotl(a + f + 0x655B59C3 + b12,  6); a = t;
            f = c ^ (b | ~d); t = d; d = c; c = b; b += _lrotl(a + f + 0x8F0CCC92 + b3,  10); a = t;
            f = c ^ (b | ~d); t = d; d = c; c = b; b += _lrotl(a + f + 0xFFEFF47D + b10, 15); a = t;
            f = c ^ (b | ~d); t = d; d = c; c = b; b += _lrotl(a + f + 0x85845DD1 + b1,  21); a = t;
            f = c ^ (b | ~d); t = d; d = c; c = b; b += _lrotl(a + f + 0x6FA87E4F + b8,   6); a = t;
            f = c ^ (b | ~d); t = d; d = c; c = b; b += _lrotl(a + f + 0xFE2CE6E0 + b15, 10); a = t;
            f = c ^ (b | ~d); t = d; d = c; c = b; b += _lrotl(a + f + 0xA3014314 + b6,  15); a = t;
            f = c ^ (b | ~d); t = d; d = c; c = b; b += _lrotl(a + f + 0x4E0811A1 + b13, 21); a = t;
            f = c ^ (b | ~d); t = d; d = c; c = b; b += _lrotl(a + f + 0xF7537E82 + b4,   6); a = t;
            f = c ^ (b | ~d); t = d; d = c; c = b; b += _lrotl(a + f + 0xBD3AF235 + b11, 10); a = t;
            f = c ^ (b | ~d); t = d; d = c; c = b; b += _lrotl(a + f + 0x2AD7D2BB + b2,  15); a = t;
            f = c ^ (b | ~d); t = d; d = c; c = b; b += _lrotl(a + f + 0xEB86D391 + b9,  21); a = t;

            h0 += a;
            h1 += b;
            h2 += c;
            h3 += d;
        }
    }
    PutUINT32LittleEndian(&Hash[0], h0);
    PutUINT32LittleEndian(&Hash[4], h1);
    PutUINT32LittleEndian(&Hash[8], h2);
    PutUINT32LittleEndian(&Hash[12], h3);
}
