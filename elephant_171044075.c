#include <stdio.h>
#include <assert.h>
#include <stdlib.h>
#include <string.h>

// CAN DUYAR - 171044075 /Elephant algorithm implementation

#define KEEPBYTES 16
#define SIZEOFBLOCKS 25
#define ELEPHANTBYTES 64
#define ELEPHANT_NPUBBYTES 12
#define BYTESOFKEY 16
#define roundMax 18
#define index(a, b) (((a)%5)+5*((b)%5))
typedef unsigned char BYTEDEF;
typedef unsigned long long LEN;
const unsigned int KeccakList[25] = {
    0, 1, 6, 4, 3, 4, 4, 6, 7, 4, 3, 2, 3, 1, 7, 1, 5, 7, 5, 0, 2, 2, 5, 0, 6
};

//kRound means Keccak Round
const BYTEDEF kRound[roundMax] = {
    0x01, 0x82, 0x8a, 0x00, 0x8b, 0x01, 0x81, 0x09, 0x8a,
    0x88, 0x09, 0x0a, 0x8b, 0x8b, 0x89, 0x03, 0x02, 0x80
};


//Left shifting function
#define RotateLeft8(a, offset) ((offset != 0) ? ((((BYTEDEF)a) << offset) ^ (((BYTEDEF)a) >> (sizeof(BYTEDEF)*8-offset))) : a)

//left shifting
BYTEDEF rotateLeft(BYTEDEF param)
{
    return (param << 1) | (param >> 7);
}


int elephantCmp(const BYTEDEF* a, const BYTEDEF* b, LEN length)
{
    BYTEDEF r = 0;

    for (LEN i = 0; i < length; ++i)
        r |= a[i] ^ b[i];
    return r;
}

//lfsr
void LFSRpart(BYTEDEF* out, BYTEDEF* in)
{
    BYTEDEF keep = rotateLeft(in[0]) ^ rotateLeft(in[2]) ^ (in[13] << 1);
    for(LEN t = 0; t < SIZEOFBLOCKS - 1; ++t)
        out[t] = in[t + 1];
    out[SIZEOFBLOCKS - 1] = keep;
}

// XOR
void XORdesign(BYTEDEF* step, const BYTEDEF* design, LEN length)
{
    for(LEN t = 0; t < length; ++t)
        step[t] ^= design[t];
}


void relatedDataBlock(BYTEDEF* out, const BYTEDEF* relatedData, LEN lenData, const BYTEDEF* n, LEN t)
{
    const LEN offset = t * SIZEOFBLOCKS - (t != 0) * ELEPHANT_NPUBBYTES;
    LEN len = 0;

    if(t == 0) {
        memcpy(out, n, ELEPHANT_NPUBBYTES);
        len += ELEPHANT_NPUBBYTES;
    }

    if(t != 0 && offset == lenData) {
        memset(out, 0x00, SIZEOFBLOCKS);
        out[0] = 0x01;
        return;
    }
    const LEN r_out = SIZEOFBLOCKS - len;
    const LEN r_data  = lenData - offset;

    if(r_out <= r_data) {
        memcpy(out + len, relatedData + offset, r_out);
    } else {
        if(r_data > 0)
            memcpy(out + len, relatedData + offset, r_data);
        memset(out + len + r_data, 0x00, r_out - r_data);
        out[len + r_data] = 0x01;
    }
}

void get_c_block(BYTEDEF* out, const BYTEDEF* c, LEN text, LEN t)
{
    const LEN offset = t * SIZEOFBLOCKS;

    if(offset == text) {
        memset(out, 0x00, SIZEOFBLOCKS);
        out[0] = 0x01;
        return;
    }
    const LEN r_text  = text - offset;

    if(SIZEOFBLOCKS <= r_text) {
        memcpy(out, c + offset, SIZEOFBLOCKS);
    } else {
        if(r_text > 0) // c might be nullptr
            memcpy(out, c + offset, r_text);
        memset(out + r_text, 0x00, SIZEOFBLOCKS - r_text);
        out[r_text] = 0x01;
    }
}

void fun(BYTEDEF *GTU)
{
    unsigned int a, b;
    BYTEDEF ARR[5], ARR2[5];

    for(a=0; a<5; a++) {
        ARR[a] = 0;
        for(b=0; b<5; b++)
            ARR[a] ^= GTU[index(a, b)];
    }
    for(a=0; a<5; a++)
        ARR2[a] = RotateLeft8(ARR[(a+1)%5], 1) ^ ARR[(a+4)%5];
    for(a=0; a<5; a++)
        for(b=0; b<5; b++)
            GTU[index(a, b)] ^= ARR2[a];
}



void fun2(BYTEDEF *GTU)
{
    for(unsigned int a=0; a<5; a++)
        for(unsigned int b=0; b<5; b++)
            GTU[index(a, b)] = RotateLeft8(GTU[index(a, b)], KeccakList[index(a, b)]);
}

void fun3(BYTEDEF *GTU)
{
    BYTEDEF keep[25];

    for(unsigned int a=0; a<5; a++)
        for(unsigned int b=0; b<5; b++)
            keep[index(a, b)] = GTU[index(a, b)];
    for(unsigned int a=0; a<5; a++)
        for(unsigned int b=0; b<5; b++)
            GTU[index(0*a+1*b, 2*a+3*b)] = keep[index(a, b)];
}

void fun4(BYTEDEF *GTU)
{
    unsigned int a, b;
    BYTEDEF ARR[5];

    for(b=0; b<5; b++) {
        for(a=0; a<5; a++)
            ARR[a] = GTU[index(a, b)] ^ ((~GTU[index(a+1, b)]) & GTU[index(a+2, b)]);
        for(a=0; a<5; a++)
            GTU[index(a, b)] = ARR[a];
    }
}

void fun5(BYTEDEF *GTU, unsigned int ind)
{
    GTU[index(0, 0)] ^= kRound[ind];
}


// P 200 version based on Keccak Permutation
void P200version(BYTEDEF *current, unsigned int ind)
{
    fun(current);
    fun2(current);
    fun3(current);
    fun4(current);
    fun5(current, ind);
}

//for Keccak permutation part
void permutation(BYTEDEF* param)
{
    for(unsigned int t=0; t<roundMax; t++)
        P200version(param, t);
}


void implementationCrypto(
    BYTEDEF* c, BYTEDEF* label, const BYTEDEF* m, LEN lengthMessage, const BYTEDEF* relatedData, LEN dataLen,
    const BYTEDEF* n, const BYTEDEF* k, int encrypt)
{

    const LEN numberOfBlocks  = 1 + lengthMessage / SIZEOFBLOCKS;
    const LEN numberOfBlocks2  = (lengthMessage % SIZEOFBLOCKS) ? numberOfBlocks : numberOfBlocks - 1;
    const LEN numberOfBlocksData = 1 + (ELEPHANT_NPUBBYTES + dataLen) / SIZEOFBLOCKS;
    const LEN it = (numberOfBlocks > numberOfBlocksData) ? numberOfBlocks : numberOfBlocksData + 1;

    BYTEDEF expKey[SIZEOFBLOCKS] = {0};
    memcpy(expKey, k, BYTESOFKEY);
    permutation(expKey);

    BYTEDEF buffer_back[SIZEOFBLOCKS] = {0};
    BYTEDEF buffer_current[SIZEOFBLOCKS] = {0};
    BYTEDEF buffer_forward[SIZEOFBLOCKS] = {0};
    memcpy(buffer_current, expKey, SIZEOFBLOCKS);

    BYTEDEF* previous = buffer_back;
    BYTEDEF* current = buffer_current;
    BYTEDEF* next = buffer_forward;

    BYTEDEF elephantBuffer[SIZEOFBLOCKS];

    BYTEDEF label_buffer[SIZEOFBLOCKS] = {0};
    memset(label, 0, KEEPBYTES);

    LEN offset = 0;
    for(LEN t = 0; t < it; ++t) {
        LFSRpart(next, current);

        if(t < numberOfBlocks2) {
            memcpy(elephantBuffer, n, ELEPHANT_NPUBBYTES);
            memset(elephantBuffer + ELEPHANT_NPUBBYTES, 0, SIZEOFBLOCKS - ELEPHANT_NPUBBYTES);
            XORdesign(elephantBuffer, current, SIZEOFBLOCKS);
            permutation(elephantBuffer);
            XORdesign(elephantBuffer, current, SIZEOFBLOCKS);
            const LEN r_len = (t == numberOfBlocks2 - 1) ? lengthMessage - offset : SIZEOFBLOCKS;
            XORdesign(elephantBuffer, m + offset, r_len);
            memcpy(c + offset, elephantBuffer, r_len);
        }

        if(t < numberOfBlocks) {
            get_c_block(label_buffer, encrypt ? c : m, lengthMessage, t);
            XORdesign(label_buffer, current, SIZEOFBLOCKS);
            XORdesign(label_buffer, next, SIZEOFBLOCKS);
            permutation(label_buffer);
            XORdesign(label_buffer, current, SIZEOFBLOCKS);
            XORdesign(label_buffer, next, SIZEOFBLOCKS);
            XORdesign(label, label_buffer, KEEPBYTES);
        }

        if(t > 0 && t <= numberOfBlocksData) {
            relatedDataBlock(label_buffer,relatedData,dataLen, n, t - 1);
            XORdesign(label_buffer, previous, SIZEOFBLOCKS);
            XORdesign(label_buffer, next, SIZEOFBLOCKS);
            permutation(label_buffer);
            XORdesign(label_buffer, previous, SIZEOFBLOCKS);
            XORdesign(label_buffer, next, SIZEOFBLOCKS);
            XORdesign(label, label_buffer, KEEPBYTES);
        }

        BYTEDEF* const keep = previous;
        previous = current;
        current = next;
        next = keep;

        offset += SIZEOFBLOCKS;
    }
}


int elephantEncryption(
  unsigned char *c, unsigned long long *len,
  const unsigned char *m, unsigned long long lengthMessage,
  const unsigned char *relatedData, unsigned long long dataLen,
  const unsigned char *ns,
  const unsigned char *n,
  const unsigned char *k)
{
    (void)ns;
    *len = lengthMessage + KEEPBYTES;
    BYTEDEF label[KEEPBYTES];
    implementationCrypto(c, label, m, lengthMessage, relatedData, dataLen, n, k, 1);
    memcpy(c + lengthMessage, label, KEEPBYTES);
    return 0;
}

int elephantDecryption(
  unsigned char *m, unsigned long long *lengthMessage,
  unsigned char *ns,
  const unsigned char *c, unsigned long long len,
  const unsigned char *relatedData, unsigned long long dataLen,
  const unsigned char *n,
  const unsigned char *k)
{
    (void)ns;
    if(len < KEEPBYTES)
        return -1;
    *lengthMessage = len - KEEPBYTES;
    BYTEDEF label[KEEPBYTES];
    implementationCrypto(m, label, c, *lengthMessage, relatedData, dataLen, n, k, 0);
    return (elephantCmp(c + *lengthMessage, label, KEEPBYTES) == 0) ? 0 : -1;
}



void s2h(unsigned char* in, int len, char* out)
{
    int turn;
    int t;
    t=0;
    turn=0;

    for (t=0;t<len;t+=2){
        sprintf((char*)(out+t),"%02X", in[turn]);
        turn+=1;
    }
    out[t++] = '\0';
}


void *h2b(char *hex, unsigned char* bytes ) {
    int t;
    int len = strlen(hex);

    for (t = 0; t < (len / 2); t++) {
        sscanf(hex + 2*t, "%02hhx", &bytes[t]);
    }
}

// TEST
int main (int argc, char *argv[]) {

  unsigned long long lenMessage;
  unsigned long long len;
  unsigned char plaintext[ELEPHANTBYTES];
  unsigned char cipher[ELEPHANTBYTES];
  unsigned char n[ELEPHANT_NPUBBYTES]="";
  unsigned char relatedData[KEEPBYTES]="";
  unsigned char ns[KEEPBYTES]="";
  unsigned char key[BYTESOFKEY];

  char pl[ELEPHANTBYTES]="gtuceng";
  char hex[ELEPHANTBYTES]="";
  char keyhex[2*BYTESOFKEY+1]="0123456789ABCDEF0123456789ABCDEF";
  char nonce[2*ELEPHANT_NPUBBYTES+1]="000000000000111111111111";
  char additional[KEEPBYTES]="gtuceng";

  strcpy(plaintext,pl);
  strcpy(relatedData,additional);
  h2b(keyhex,key);
  h2b(nonce,n);

  printf("Test of the Elephant light-weight cipher\n");
  printf("Plaintext: %s\n",plaintext);
  printf("Key: %s\n",keyhex);
  printf("Nonce: %s\n",nonce);
  printf("Additional Information: %s\n\n",relatedData);

  printf("Plaintext: %s\n",plaintext);
  int temp = elephantEncryption(cipher,&len,plaintext,strlen(plaintext),relatedData,strlen(relatedData),ns,n,key);

  s2h(cipher,len,hex);

  printf("Cipher: %s, Length of the Cipher: %llu\n",hex, len);

  temp = elephantDecryption(plaintext,&lenMessage,ns,cipher,len,relatedData,strlen(relatedData),n,key);

  printf("Plaintext: %s, length of the Plaintext: %llu\n",plaintext, lenMessage);

  if (temp==0) {
    printf("Elephant Cipher passed from the test successfully!\n");
  }

	return 0;
}
